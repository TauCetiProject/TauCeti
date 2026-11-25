/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units

/-!
# The general spin group

The *general spin group* `GSpin(Q)` of a quadratic form is the group of even elements of the
Lipschitz group, that is, of the units of the even Clifford algebra which are products of an even
number of vectors of invertible norm. This is the classical description of the rational points of
the reductive group `GSpin` attached to a nondegenerate quadratic space, one of the split classical
groups alongside `Sp` and `SO`. Compared with the Spin group it keeps all scalar units instead of
only the square roots of unity: over a field, the vector action of `GSpin(Q)` is onto `SO(Q)` with
kernel the multiplicative group, while on `Spin(Q)` it has kernel `{±1}` and image the kernel of
the spinor norm. The exact sequence for `GSpin(Q)` is proved in
`TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.SpecialOrthogonal`.

This file defines the group and the structure attached to it.

* The *central cocharacter* `e₀∨ : Rˣ → GSpin(Q)`, `a ↦ a`, is the inclusion of the scalar units.
  It exists as soon as some vector has invertible norm, which for a nondegenerate form over a field
  of characteristic other than two means positive dimension; on the zero space the Lipschitz group
  is trivial. It is central, and
  injective when `2` is invertible.
* The *Clifford norm* `ν : GSpin(Q) → Rˣ`, `x ↦ star x * x`, is the restriction of
  `CliffordAlgebra.lipschitzNorm`; like the latter it is defined when `2` is invertible. It is
  the similitude character of `GSpin`: it squares the central cocharacter, `ν (e₀∨ a) = a * a`,
  and its kernel is exactly the Spin group.
* `GSpin(Q)` is functorial in quadratic isometries and compatible with extension of scalars.

## Main definitions

* `CliffordAlgebra.gSpinGroup Q`: the general spin group, as a subgroup of the Clifford units.
* `CliffordAlgebra.gSpinToLipschitz Q`: its inclusion into the Lipschitz group.
* `CliffordAlgebra.spinToGSpin Q`: the inclusion of Mathlib's Spin group.
* `CliffordAlgebra.gSpinNorm Q`: the Clifford norm `GSpin(Q) →* Rˣ`.
* `CliffordAlgebra.gSpinScalarUnits Q hQ`: the central cocharacter `Rˣ →* GSpin(Q)`.
* `QuadraticMap.Isometry.gSpinGroupMap f` and `QuadraticMap.IsometryEquiv.gSpinGroupEquiv e`: the
  maps induced by quadratic isometries.
* `CliffordAlgebra.gSpinGroupBaseChange Q`: extension of scalars.

## Main results

* `CliffordAlgebra.mem_gSpinGroup_iff`: `GSpin(Q)` consists of the even Lipschitz elements.
* `CliffordAlgebra.range_spinToGSpin`: the Spin group is the kernel of the Clifford norm.
* `CliffordAlgebra.gSpinNorm_gSpinScalarUnits`: the norm of `e₀∨ a` is `a * a`.
* `CliffordAlgebra.gSpinScalarUnits_mem_center` and `CliffordAlgebra.gSpinScalarUnits_injective`:
  the central cocharacter is central, and injective when `2` is invertible.
* `CliffordAlgebra.gSpinGroupBaseChange_gSpinScalarUnits`: extension of scalars is compatible with
  the central cocharacter.
* `CliffordAlgebra.gSpinNorm_gSpinGroupBaseChange` and
  `QuadraticMap.Isometry.gSpinNorm_gSpinGroupMap`: the Clifford norm is compatible with extension
  of scalars and with quadratic isometries.
* `CliffordAlgebra.gSpinGroupBaseChange_spinToGSpin` and
  `QuadraticMap.Isometry.gSpinGroupMap_spinToGSpin`: the inclusion of the Spin group is compatible
  with extension of scalars and with quadratic isometries.

## References

* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2, for
  `GSpin` and its central cocharacter.
* Y. Cai, S. Friedberg, E. Kaplan, *Doubling constructions: local and global theory, with an
  application to global functoriality for non-generic cuspidal representations*, §1.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

universe u v w

namespace CliffordAlgebra

open TauCeti

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- The **general spin group** `GSpin(Q)`: the elements of the Lipschitz group lying in the even
Clifford subalgebra. -/
def gSpinGroup : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {x | x ∈ lipschitzGroup Q ∧ (x : CliffordAlgebra Q) ∈ even Q}
  one_mem' := ⟨one_mem _, Subalgebra.one_mem _⟩
  mul_mem' hx hy := ⟨mul_mem hx.1 hy.1, Subalgebra.mul_mem _ hx.2 hy.2⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by
    have h := hx.2
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h ⊢
    simpa only [neg_zero] using x.val_inv_mem_graded (𝒜 := evenOdd Q) h⟩

variable {Q} in
/-- A Clifford unit lies in `GSpin(Q)` exactly when it is an even element of the Lipschitz
group. -/
@[simp]
theorem mem_gSpinGroup_iff {x : (CliffordAlgebra Q)ˣ} :
    x ∈ gSpinGroup Q ↔ x ∈ lipschitzGroup Q ∧ (x : CliffordAlgebra Q) ∈ even Q :=
  Iff.rfl

/-- `GSpin(Q)` is a subgroup of the Lipschitz group. -/
theorem gSpinGroup_le_lipschitzGroup : gSpinGroup Q ≤ lipschitzGroup Q := fun _ hx ↦ hx.1

variable {Q} in
/-- An element of `GSpin(Q)` is even. -/
theorem gSpinGroup.coe_mem_even (x : gSpinGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
  x.property.2

/-! ### The Lipschitz and Spin groups -/

/-- The inclusion of `GSpin(Q)` into the Lipschitz group. -/
def gSpinToLipschitz : gSpinGroup Q →* lipschitzGroup Q :=
  Subgroup.inclusion (gSpinGroup_le_lipschitzGroup Q)

/-- An element of `GSpin(Q)` is included in the Lipschitz group as itself. -/
@[simp]
theorem coe_gSpinToLipschitz_apply (x : gSpinGroup Q) :
    ((gSpinToLipschitz Q x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) = x :=
  (rfl)

/-- The inclusion of `GSpin(Q)` into the Lipschitz group is injective. -/
theorem gSpinToLipschitz_injective : Function.Injective (gSpinToLipschitz Q) :=
  Subgroup.inclusion_injective _

/-- The range of the inclusion into the Lipschitz group consists of the even Lipschitz
elements. -/
theorem mem_range_gSpinToLipschitz_iff (x : lipschitzGroup Q) :
    x ∈ (gSpinToLipschitz Q).range ↔ ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property.2, fun hx ↦ ⟨⟨x, x.property, hx⟩, rfl⟩⟩

/-- The inclusion of Mathlib's Spin group `Spin(Q) = Pin(Q) ⊓ even` into `GSpin(Q)`. -/
def spinToGSpin : spinGroup Q →* gSpinGroup Q :=
  spinGroup.toUnits.codRestrict _ fun x ↦
    ⟨spinGroup.units_mem_lipschitzGroup x.property, by
      rw [spinGroup.val_toUnits_apply]
      exact spinGroup.mem_even x.property⟩

/-- A Spin element is included in `GSpin(Q)` as itself. -/
@[simp]
theorem coe_spinToGSpin_apply (x : spinGroup Q) :
    (((spinToGSpin Q x : gSpinGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = x :=
  spinGroup.val_toUnits_apply x

/-- The inclusion of the Spin group into `GSpin(Q)` is injective. -/
theorem spinToGSpin_injective : Function.Injective (spinToGSpin Q) := fun x y h ↦
  Subtype.ext <| by
    simpa only [coe_spinToGSpin_apply] using
      congrArg (fun z : gSpinGroup Q ↦ ((z : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h

/-- Including Spin into `GSpin` and then into the Lipschitz group is the canonical inclusion of
Spin into the Lipschitz group. -/
@[simp]
theorem gSpinToLipschitz_spinToGSpin (x : spinGroup Q) :
    gSpinToLipschitz Q (spinToGSpin Q x) = spinToLipschitz Q x :=
  Subtype.ext <| Units.ext <| by
    rw [coe_gSpinToLipschitz_apply, coe_spinToGSpin_apply, coe_spinToLipschitz_apply]

/-! ### The Clifford norm -/

section Norm

variable [Invertible (2 : R)]

/-- The **Clifford norm** `x ↦ star x * x` of `GSpin(Q)`, a unit scalar: the restriction of
`CliffordAlgebra.lipschitzNorm`. This is the similitude character of the general spin group. -/
noncomputable def gSpinNorm : gSpinGroup Q →* Rˣ :=
  (lipschitzNorm Q).comp (gSpinToLipschitz Q)

/-- The Clifford norm of `GSpin(Q)` is the restriction of the norm of the Lipschitz group. -/
@[simp]
theorem lipschitzNorm_gSpinToLipschitz (x : gSpinGroup Q) :
    lipschitzNorm Q (gSpinToLipschitz Q x) = gSpinNorm Q x :=
  (rfl)

/-- The Clifford conjugate of an element of `GSpin(Q)` times the element is its norm. -/
@[simp]
theorem star_mul_self_eq_algebraMap_gSpinNorm (x : gSpinGroup Q) :
    star ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (gSpinNorm Q x : R) :=
  star_mul_self_eq_algebraMap_lipschitzNorm Q (gSpinToLipschitz Q x)

/-- An element of `GSpin(Q)` times its Clifford conjugate is its norm. -/
@[simp]
theorem self_mul_star_eq_algebraMap_gSpinNorm (x : gSpinGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        star ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (gSpinNorm Q x : R) :=
  self_mul_star_eq_algebraMap_lipschitzNorm Q (gSpinToLipschitz Q x)

/-- An element of `GSpin(Q)` lies in the Spin group exactly when its Clifford norm is one. -/
theorem coe_mem_spinGroup_iff_gSpinNorm_eq_one (x : gSpinGroup Q) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ spinGroup Q ↔ gSpinNorm Q x = 1 := by
  rw [spinGroup.mem_iff, ← lipschitzNorm_gSpinToLipschitz,
    ← mem_pinGroup_iff_lipschitzNorm_eq_one, coe_gSpinToLipschitz_apply]
  exact and_iff_left (gSpinGroup.coe_mem_even x)

/-- **The Spin group is the kernel of the Clifford norm on `GSpin(Q)`.** -/
theorem range_spinToGSpin : (spinToGSpin Q).range = (gSpinNorm Q).ker := by
  ext x
  rw [MonoidHom.mem_ker, ← coe_mem_spinGroup_iff_gSpinNorm_eq_one]
  refine ⟨fun ⟨y, hy⟩ ↦ hy ▸ (coe_spinToGSpin_apply Q y).symm ▸ y.property, fun hx ↦
    ⟨⟨_, hx⟩, Subtype.ext (Units.ext (coe_spinToGSpin_apply Q _))⟩⟩

/-- A Spin element has Clifford norm one. -/
@[simp]
theorem gSpinNorm_spinToGSpin (x : spinGroup Q) : gSpinNorm Q (spinToGSpin Q x) = 1 :=
  (coe_mem_spinGroup_iff_gSpinNorm_eq_one Q _).1 ((coe_spinToGSpin_apply Q x).symm ▸ x.property)

end Norm

/-! ### The central cocharacter -/

/-- The **central cocharacter** `e₀∨ : Rˣ →* GSpin(Q)`, the inclusion `a ↦ a` of the scalar
units. It is defined as soon as some vector has invertible norm; on the zero space the Lipschitz
group, hence `GSpin(Q)`, is trivial. -/
noncomputable def gSpinScalarUnits (hQ : ∃ v, IsUnit (Q v)) : Rˣ →* gSpinGroup Q :=
  (Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom).codRestrict _ fun a ↦
    ⟨unitsMap_algebraMap_mem_lipschitzGroup hQ a, Subalgebra.algebraMap_mem _ _⟩

variable {Q}

/-- The central cocharacter sends `a` to the scalar `a` of the Clifford algebra. -/
@[simp]
theorem coe_gSpinScalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    (((gSpinScalarUnits Q hQ a : gSpinGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) a :=
  (rfl)

/-- The central cocharacter, followed by the inclusion into the Lipschitz group, is the group of
scalar units of the Lipschitz group. -/
@[simp]
theorem gSpinToLipschitz_gSpinScalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    gSpinToLipschitz Q (gSpinScalarUnits Q hQ a) = scalarUnits Q hQ a :=
  Subtype.ext <| Units.ext <| by
    rw [coe_gSpinToLipschitz_apply, coe_gSpinScalarUnits, coe_scalarUnits]

/-- The central cocharacter is injective when `2` is invertible. -/
theorem gSpinScalarUnits_injective [Invertible (2 : R)] (hQ : ∃ v, IsUnit (Q v)) :
    Function.Injective (gSpinScalarUnits Q hQ) := fun a b hab ↦
  scalarUnits_injective hQ (by
    rw [← gSpinToLipschitz_gSpinScalarUnits, ← gSpinToLipschitz_gSpinScalarUnits, hab])

/-- The central cocharacter takes values in the centre of `GSpin(Q)`. -/
theorem gSpinScalarUnits_mem_center (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    gSpinScalarUnits Q hQ a ∈ Subgroup.center (gSpinGroup Q) :=
  Subgroup.mem_center_iff.2 fun x ↦ Subtype.ext <| Units.ext <| by
    simp only [Subgroup.coe_mul, Units.val_mul, coe_gSpinScalarUnits]
    exact (Algebra.commutes _ _).symm

/-- The range of the central cocharacter is contained in the centre of `GSpin(Q)`. -/
theorem range_gSpinScalarUnits_le_center (hQ : ∃ v, IsUnit (Q v)) :
    (gSpinScalarUnits Q hQ).range ≤ Subgroup.center (gSpinGroup Q) := by
  rintro _ ⟨a, rfl⟩
  exact gSpinScalarUnits_mem_center hQ a

/-- **The Clifford norm squares the central cocharacter**: `ν (e₀∨ a) = a * a`. -/
@[simp]
theorem gSpinNorm_gSpinScalarUnits [Invertible (2 : R)] (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    gSpinNorm Q (gSpinScalarUnits Q hQ a) = a * a := by
  rw [← lipschitzNorm_gSpinToLipschitz, gSpinToLipschitz_gSpinScalarUnits,
    lipschitzNorm_scalarUnits]

end CommRing

/-! ### Extension of scalars -/

section BaseChange

open scoped TensorProduct

variable {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Invertible (2 : R)] (Q : QuadraticForm R M)

/-- The homomorphism `GSpin(Q) →* GSpin(Q_A)` induced by extension of scalars, the restriction of
`CliffordAlgebra.lipschitzGroupBaseChange`. -/
noncomputable def gSpinGroupBaseChange : gSpinGroup Q →* gSpinGroup (Q.baseChange A) :=
  (((lipschitzGroup (Q.baseChange A)).subtype.comp (lipschitzGroupBaseChange (A := A) Q)).comp
      (gSpinToLipschitz Q)).codRestrict _ fun x ↦
    ⟨(lipschitzGroupBaseChange (A := A) Q (gSpinToLipschitz Q x)).property, by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        coe_lipschitzGroupBaseChange_apply, coe_gSpinToLipschitz_apply]
      exact ofBaseChangeAux_mem_even Q (gSpinGroup.coe_mem_even x)⟩

variable {Q}

/-- Extension of scalars on `GSpin` is the restriction of extension of scalars on the Lipschitz
group. -/
@[simp]
theorem gSpinToLipschitz_gSpinGroupBaseChange (x : gSpinGroup Q) :
    gSpinToLipschitz (Q.baseChange A) (gSpinGroupBaseChange (A := A) Q x) =
      lipschitzGroupBaseChange (A := A) Q (gSpinToLipschitz Q x) :=
  (rfl)

/-- Extension of scalars on `GSpin` is the canonical Clifford algebra map
`CliffordAlgebra.ofBaseChangeAux`. -/
@[simp]
theorem coe_gSpinGroupBaseChange_apply (x : gSpinGroup Q) :
    (((gSpinGroupBaseChange (A := A) Q x : gSpinGroup (Q.baseChange A)) :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [← coe_gSpinToLipschitz_apply, gSpinToLipschitz_gSpinGroupBaseChange,
    coe_lipschitzGroupBaseChange_apply, coe_gSpinToLipschitz_apply]

/-- **Extension of scalars is compatible with the central cocharacter**: it sends `e₀∨ a` to
`e₀∨` of the image of `a`. -/
@[simp]
theorem gSpinGroupBaseChange_gSpinScalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    gSpinGroupBaseChange (A := A) Q (gSpinScalarUnits Q hQ a) =
      gSpinScalarUnits (Q.baseChange A) (QuadraticForm.exists_isUnit_baseChange (A := A) hQ)
        (Units.map (algebraMap R A) a) :=
  gSpinToLipschitz_injective _ <| by
    rw [gSpinToLipschitz_gSpinGroupBaseChange, gSpinToLipschitz_gSpinScalarUnits,
      gSpinToLipschitz_gSpinScalarUnits, lipschitzGroupBaseChange_scalarUnits]

/-- **Extension of scalars is compatible with the Clifford norm**: the norm of the extension of
`x` is the image of the norm of `x`. -/
@[simp]
theorem gSpinNorm_gSpinGroupBaseChange [Invertible (2 : A)] (x : gSpinGroup Q) :
    gSpinNorm (Q.baseChange A) (gSpinGroupBaseChange (A := A) Q x) =
      Units.map (algebraMap R A) (gSpinNorm Q x) :=
  Units.ext <| algebraMap_injective (Q.baseChange A) <| by
    rw [← star_mul_self_eq_algebraMap_gSpinNorm, coe_gSpinGroupBaseChange_apply,
      ← ofBaseChangeAux_star, ← map_mul, star_mul_self_eq_algebraMap_gSpinNorm, AlgHom.commutes,
      Units.coe_map, MonoidHom.coe_ofClass, ← IsScalarTower.algebraMap_apply]

/-- Extension of scalars followed by the Clifford norm is the Clifford norm followed by the map
on units induced by `algebraMap`. -/
theorem gSpinNorm_comp_gSpinGroupBaseChange [Invertible (2 : A)] :
    (gSpinNorm (Q.baseChange A)).comp (gSpinGroupBaseChange (A := A) Q) =
      (Units.map (algebraMap R A)).comp (gSpinNorm Q) :=
  MonoidHom.ext gSpinNorm_gSpinGroupBaseChange

/-- **Extension of scalars is compatible with the inclusion of Spin**: it sends a Spin element,
viewed in `GSpin(Q)`, to its scalar extension in the Spin group of `Q_A`. -/
@[simp]
theorem gSpinGroupBaseChange_spinToGSpin (x : spinGroup Q) :
    gSpinGroupBaseChange (A := A) Q (spinToGSpin Q x) =
      spinToGSpin (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_gSpinGroupBaseChange_apply, coe_spinToGSpin_apply, coe_spinToGSpin_apply,
      coe_spinGroupBaseChange_apply]

/-- The inclusion of Spin followed by extension of scalars on `GSpin` is extension of scalars on
Spin followed by the inclusion of Spin. -/
theorem gSpinGroupBaseChange_comp_spinToGSpin :
    (gSpinGroupBaseChange (A := A) Q).comp (spinToGSpin Q) =
      (spinToGSpin (Q.baseChange A)).comp (spinGroupBaseChange (A := A) Q) :=
  MonoidHom.ext gSpinGroupBaseChange_spinToGSpin

end BaseChange

end CliffordAlgebra

/-! ### Functoriality in quadratic isometries -/

namespace QuadraticMap.Isometry

open CliffordAlgebra

universe x

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- The homomorphism `GSpin(Q₁) →* GSpin(Q₂)` induced by a quadratic isometry, the restriction of
its Clifford algebra map. -/
def gSpinGroupMap (f : Q₁ →qᵢ Q₂) : gSpinGroup Q₁ →* gSpinGroup Q₂ :=
  (((lipschitzGroup Q₂).subtype.comp f.lipschitzGroupMap).comp (gSpinToLipschitz Q₁)).codRestrict
    _ fun x ↦ ⟨(f.lipschitzGroupMap (gSpinToLipschitz Q₁ x)).property, by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        coe_lipschitzGroupMap_apply, coe_gSpinToLipschitz_apply]
      exact map_mem_even f (gSpinGroup.coe_mem_even x)⟩

/-- The map on `GSpin` induced by an isometry is the restriction of the induced map on Lipschitz
groups. -/
@[simp]
theorem gSpinToLipschitz_gSpinGroupMap (f : Q₁ →qᵢ Q₂) (x : gSpinGroup Q₁) :
    gSpinToLipschitz Q₂ (f.gSpinGroupMap x) = f.lipschitzGroupMap (gSpinToLipschitz Q₁ x) :=
  (rfl)

/-- The map on `GSpin` induced by an isometry is its Clifford algebra map. -/
@[simp]
theorem coe_gSpinGroupMap_apply (f : Q₁ →qᵢ Q₂) (x : gSpinGroup Q₁) :
    (((f.gSpinGroupMap x : gSpinGroup Q₂) : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) =
      CliffordAlgebra.map f ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) := by
  rw [← coe_gSpinToLipschitz_apply, gSpinToLipschitz_gSpinGroupMap, coe_lipschitzGroupMap_apply,
    coe_gSpinToLipschitz_apply]

/-- The identity isometry induces the identity of `GSpin`. -/
@[simp]
theorem gSpinGroupMap_id (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.Isometry.id Q₁).gSpinGroupMap = MonoidHom.id (gSpinGroup Q₁) :=
  MonoidHom.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [coe_gSpinGroupMap_apply, MonoidHom.id_apply]
    exact AlgHom.congr_fun (CliffordAlgebra.map_id Q₁) _

/-- The maps induced on `GSpin` respect composition of quadratic isometries. -/
@[simp]
theorem gSpinGroupMap_comp (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    f.gSpinGroupMap.comp g.gSpinGroupMap = (f.comp g).gSpinGroupMap :=
  MonoidHom.ext fun x ↦ Subtype.ext <| Units.ext <| by
    rw [MonoidHom.comp_apply, coe_gSpinGroupMap_apply, coe_gSpinGroupMap_apply,
      coe_gSpinGroupMap_apply]
    exact AlgHom.congr_fun (CliffordAlgebra.map_comp_map f g) _

/-- The map induced on `GSpin` by a quadratic isometry is compatible with the central
cocharacters. -/
@[simp]
theorem gSpinGroupMap_gSpinScalarUnits (f : Q₁ →qᵢ Q₂) (hQ₁ : ∃ v, IsUnit (Q₁ v)) (a : Rˣ) :
    f.gSpinGroupMap (gSpinScalarUnits Q₁ hQ₁ a) =
      gSpinScalarUnits Q₂ (f.exists_isUnit_apply hQ₁) a :=
  Subtype.ext <| Units.ext <| by
    rw [coe_gSpinGroupMap_apply, coe_gSpinScalarUnits, coe_gSpinScalarUnits]
    exact (CliffordAlgebra.map f).commutes (a : R)

/-- **The map induced on `GSpin` by a quadratic isometry preserves the Clifford norm.** -/
@[simp]
theorem gSpinNorm_gSpinGroupMap [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂) (x : gSpinGroup Q₁) :
    gSpinNorm Q₂ (f.gSpinGroupMap x) = gSpinNorm Q₁ x :=
  Units.ext <| algebraMap_injective Q₂ <| by
    rw [← star_mul_self_eq_algebraMap_gSpinNorm, coe_gSpinGroupMap_apply,
      ← CliffordAlgebra.map_star, ← map_mul, star_mul_self_eq_algebraMap_gSpinNorm,
      AlgHom.commutes]

/-- The map induced on `GSpin` by a quadratic isometry, followed by the Clifford norm, is the
Clifford norm. -/
theorem gSpinNorm_comp_gSpinGroupMap [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂) :
    (gSpinNorm Q₂).comp f.gSpinGroupMap = gSpinNorm Q₁ :=
  MonoidHom.ext (gSpinNorm_gSpinGroupMap f)

/-- **The map induced on `GSpin` by a quadratic isometry is compatible with the inclusion of
Spin**: it restricts to the induced map of Spin groups. -/
@[simp]
theorem gSpinGroupMap_spinToGSpin (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) :
    f.gSpinGroupMap (spinToGSpin Q₁ x) = spinToGSpin Q₂ (f.spinGroupMap x) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_gSpinGroupMap_apply, coe_spinToGSpin_apply, coe_spinToGSpin_apply,
      coe_spinGroupMap_apply]

/-- The inclusion of Spin followed by the map induced on `GSpin` by a quadratic isometry is the
induced map of Spin groups followed by the inclusion of Spin. -/
theorem gSpinGroupMap_comp_spinToGSpin (f : Q₁ →qᵢ Q₂) :
    f.gSpinGroupMap.comp (spinToGSpin Q₁) = (spinToGSpin Q₂).comp f.spinGroupMap :=
  MonoidHom.ext (gSpinGroupMap_spinToGSpin f)

end QuadraticMap.Isometry

namespace QuadraticMap.IsometryEquiv

open CliffordAlgebra

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The equivalence `GSpin(Q₁) ≃* GSpin(Q₂)` induced by a quadratic isometry equivalence. -/
def gSpinGroupEquiv (e : Q₁.IsometryEquiv Q₂) : gSpinGroup Q₁ ≃* gSpinGroup Q₂ :=
  MonoidHom.toMulEquiv e.toIsometry.gSpinGroupMap e.symm.toIsometry.gSpinGroupMap
    (MonoidHom.ext fun x ↦ Subtype.ext <| Units.ext <| by
      rw [MonoidHom.comp_apply, QuadraticMap.Isometry.coe_gSpinGroupMap_apply,
        QuadraticMap.Isometry.coe_gSpinGroupMap_apply, MonoidHom.id_apply]
      exact (equivOfIsometry e).symm_apply_apply _)
    (MonoidHom.ext fun x ↦ Subtype.ext <| Units.ext <| by
      rw [MonoidHom.comp_apply, QuadraticMap.Isometry.coe_gSpinGroupMap_apply,
        QuadraticMap.Isometry.coe_gSpinGroupMap_apply, MonoidHom.id_apply]
      exact (equivOfIsometry e).apply_symm_apply _)

/-- The equivalence induced on `GSpin` agrees with the forward isometry map. -/
@[simp]
theorem gSpinGroupEquiv_apply (e : Q₁.IsometryEquiv Q₂) (x : gSpinGroup Q₁) :
    e.gSpinGroupEquiv x = e.toIsometry.gSpinGroupMap x :=
  (rfl)

/-- The inverse of the equivalence induced on `GSpin` agrees with the map induced by the inverse
isometry. -/
theorem gSpinGroupEquiv_symm_apply (e : Q₁.IsometryEquiv Q₂) (x : gSpinGroup Q₂) :
    e.gSpinGroupEquiv.symm x = e.symm.toIsometry.gSpinGroupMap x :=
  (rfl)

/-- The inverse of the equivalence induced on `GSpin` is induced by the inverse isometry. -/
@[simp]
theorem gSpinGroupEquiv_symm (e : Q₁.IsometryEquiv Q₂) :
    e.gSpinGroupEquiv.symm = e.symm.gSpinGroupEquiv :=
  MulEquiv.ext fun _ ↦ rfl

/-- The identity isometry induces the identity equivalence of `GSpin`. -/
@[simp]
theorem gSpinGroupEquiv_refl (Q₁ : QuadraticForm R M₁) :
    (QuadraticMap.IsometryEquiv.refl Q₁).gSpinGroupEquiv = MulEquiv.refl (gSpinGroup Q₁) :=
  MulEquiv.ext fun x ↦ DFunLike.congr_fun (QuadraticMap.Isometry.gSpinGroupMap_id Q₁) x

/-- The equivalences induced on `GSpin` respect composition of quadratic isometry
equivalences. -/
@[simp]
theorem gSpinGroupEquiv_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {Q₃ : QuadraticForm R M₃} (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (e₁₂.trans e₂₃).gSpinGroupEquiv = e₁₂.gSpinGroupEquiv.trans e₂₃.gSpinGroupEquiv :=
  MulEquiv.ext fun x ↦
    (DFunLike.congr_fun (e₂₃.toIsometry.gSpinGroupMap_comp e₁₂.toIsometry) x).symm

end QuadraticMap.IsometryEquiv
