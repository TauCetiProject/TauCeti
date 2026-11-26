/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Subring models and the local integral closure at a place

Let `P` be a place of `F / k`, let `B` be a commutative `F`-algebra whose elements are regular at
`P` (`∀ b : B, algebraMap B F b ∈ P.integers`), and let `C` be an integral closure of `B` in a
commutative `F`-algebra `F'`. Extending the local integral-closure API of
`TauCeti/FieldTheory/FunctionField/Place/Extension/Basic.lean`, this file shows that `C` maps into
`integralClosure P.integers F'` and records the induced `B`- and `C`-algebra structures on
`P.integers` and `integralClosure P.integers F'` together with their scalar towers.

As with `TauCeti.Place.algebraIntegersExtension` and
`TauCeti.Place.algebraConstantsIntegralClosure`, the algebra structures are provided as explicit
`@[instance_reducible]` definitions to be installed locally where needed, avoiding diamonds when
`B` or `C` coincides with `k`, `P.integers`, or `integralClosure P.integers F'`.

## Main definitions

* `TauCeti.Place.algebraIntegersOfForallMem`: the `B`-algebra structure on `P.integers` induced by
  `hB : ∀ b : B, algebraMap B F b ∈ P.integers`.
* `TauCeti.Place.algebraIntegralClosureOfForallMemIntegers`: the `C`-algebra structure on
  `integralClosure P.integers F'` induced when `C` is an integral closure of `B` in `F'`.

## Main results

* `TauCeti.Place.algebraMap_mem_integralClosure_of_forall_mem_integers`: if `B` maps into
  `P.integers`, any integral closure `C` of `B` in `F'` maps into `integralClosure P.integers F'`.
* `TauCeti.Place.coe_algebraMap_integersOfForallMem`,
  `TauCeti.Place.coe_algebraMap_integralClosureOfForallMemIntegers`,
  `TauCeti.Place.isScalarTower_integersOfForallMem`,
  `TauCeti.Place.isScalarTower_integersOfForallMem_extension`,
  `TauCeti.Place.isScalarTower_integersOfForallMem_integralClosure`,
  `TauCeti.Place.isScalarTower_integralClosureOfForallMemIntegers`, and
  `TauCeti.Place.isScalarTower_left_integralClosureOfForallMemIntegers`: characteristic coercions
  and scalar-tower compatibilities of these algebra structures.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1 and III.4.
-/

public section

namespace TauCeti.Place

universe u v v'

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

section Base

variable {B : Type*} [CommSemiring B] [Algebra B F]

/-- If an `F`-algebra `B` maps into the valuation ring `𝒪_P`, then `𝒪_P` is a `B`-algebra.

This is not a global instance: for `B = k` or `B = 𝒪_P` it would compete with existing algebra
structures. Install it locally together with `TauCeti.Place.isScalarTower_integersOfForallMem`,
`TauCeti.Place.isScalarTower_integersOfForallMem_extension`, or
`TauCeti.Place.isScalarTower_integersOfForallMem_integralClosure`. -/
@[instance_reducible]
noncomputable def algebraIntegersOfForallMem (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) : Algebra B P.integers :=
  ((algebraMap B F).codRestrict P.integers hB).toAlgebra

/-- Coercing the `B`-algebra map on `𝒪_P` to `F` recovers `algebraMap B F`. -/
theorem coe_algebraMap_integersOfForallMem (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) (b : B) :
    letI := P.algebraIntegersOfForallMem hB
    ((algebraMap B P.integers b : P.integers) : F) = algebraMap B F b :=
  (rfl)

/-- The `B`-algebra structure `TauCeti.Place.algebraIntegersOfForallMem` on `𝒪_P` forms a scalar
tower with `F`. -/
theorem isScalarTower_integersOfForallMem (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    IsScalarTower B P.integers F :=
  letI := P.algebraIntegersOfForallMem hB
  .of_algebraMap_eq fun _ ↦ rfl

section Extension

variable {F' : Type v'} [Semiring F'] [Algebra F F'] [Algebra B F'] [IsScalarTower B F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- In any `F`-algebra `F'`, `TauCeti.Place.algebraIntegersOfForallMem` and
`TauCeti.Place.algebraIntegersExtension` form a scalar tower `B → 𝒪_P → F'`. -/
theorem isScalarTower_integersOfForallMem_extension (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    IsScalarTower B P.integers F' :=
  letI := P.algebraIntegersOfForallMem hB
  .of_algebraMap_eq fun x ↦ IsScalarTower.algebraMap_apply B F F' x

end Extension

end Base

section IntegralClosure

variable {B : Type*} [CommRing B] [Algebra B F]

section Top

variable {F' : Type v'} [CommRing F'] [Algebra F F'] [Algebra B F'] [IsScalarTower B F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- The `B`-algebra structure `TauCeti.Place.algebraIntegersOfForallMem` on `𝒪_P` forms a scalar
tower `B → 𝒪_P → integralClosure 𝒪_P F'`. -/
theorem isScalarTower_integersOfForallMem_integralClosure (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    haveI := P.isScalarTower_integersOfForallMem_extension (F' := F') hB
    IsScalarTower B P.integers (integralClosure P.integers F') := by
  let _ := P.algebraIntegersOfForallMem hB
  have := P.isScalarTower_integersOfForallMem_extension (F' := F') hB
  exact .of_algebraMap_eq fun x ↦ Subtype.ext (IsScalarTower.algebraMap_apply B F F' x)

variable {C : Type*} [CommSemiring C] [Algebra C F'] [IsIntegralClosure C B F']

/-- If an `F`-subring `B` lands in `P.integers`, its integral closure `C` in `F'` lands in
`integralClosure P.integers F'`. -/
theorem algebraMap_mem_integralClosure_of_forall_mem_integers (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) (c : C) :
    algebraMap C F' c ∈ integralClosure P.integers F' := by
  let _ := P.algebraIntegersOfForallMem hB
  have := P.isScalarTower_integersOfForallMem_extension (F' := F') hB
  exact IsIntegral.tower_top (R := B) (A := P.integers)
    ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)

end Top

section AlgebraDef

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- If `B` maps into `𝒪_P` and `C` is an integral closure of `B` in `F'`, then the local integral
closure `integralClosure 𝒪_P F'` is a `C`-algebra.

This is not a global instance. Install it locally together with
`TauCeti.Place.isScalarTower_integralClosureOfForallMemIntegers` and
`TauCeti.Place.isScalarTower_left_integralClosureOfForallMemIntegers`. -/
@[instance_reducible]
noncomputable def algebraIntegralClosureOfForallMemIntegers (P : Place k F)
    (C : Type*) (F' : Type v') [CommRing F'] [Algebra F F'] [Algebra B F'] [IsScalarTower B F F']
    [CommSemiring C] [Algebra C F'] [IsIntegralClosure C B F']
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    Algebra C (integralClosure P.integers F') :=
  ((algebraMap C F').codRestrict (integralClosure P.integers F')
    (P.algebraMap_mem_integralClosure_of_forall_mem_integers hB)).toAlgebra

end AlgebraDef

section Tower

variable {F' : Type v'} [CommRing F'] [Algebra F F'] [Algebra B F'] [IsScalarTower B F F']
  {C : Type*} [CommSemiring C] [Algebra C F'] [IsIntegralClosure C B F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Coercing the `C`-algebra map on `integralClosure 𝒪_P F'` to `F'` recovers `algebraMap C F'`. -/
theorem coe_algebraMap_integralClosureOfForallMemIntegers (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) (c : C) :
    letI := P.algebraIntegralClosureOfForallMemIntegers C F' hB
    ((algebraMap C (integralClosure P.integers F') c : integralClosure P.integers F') : F') =
      algebraMap C F' c :=
  (rfl)

/-- The `C`-algebra structure `TauCeti.Place.algebraIntegralClosureOfForallMemIntegers` forms a
scalar tower `C → integralClosure 𝒪_P F' → F'`. -/
theorem isScalarTower_integralClosureOfForallMemIntegers (P : Place k F)
    (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegralClosureOfForallMemIntegers C F' hB
    IsScalarTower C (integralClosure P.integers F') F' :=
  letI := P.algebraIntegralClosureOfForallMemIntegers C F' hB
  .of_algebraMap_eq fun _ ↦ rfl

/-- For a compatible `B`-algebra structure on `C`, the local integral closure forms a scalar tower
`B → C → integralClosure 𝒪_P F'`. -/
theorem isScalarTower_left_integralClosureOfForallMemIntegers [Algebra B C]
    [IsScalarTower B C F'] (P : Place k F) (hB : ∀ b : B, algebraMap B F b ∈ P.integers) :
    letI := P.algebraIntegersOfForallMem hB
    letI := P.algebraIntegralClosureOfForallMemIntegers C F' hB
    haveI := P.isScalarTower_integersOfForallMem_extension (F' := F') hB
    IsScalarTower B C (integralClosure P.integers F') := by
  let _ := P.algebraIntegersOfForallMem hB
  let _ := P.algebraIntegralClosureOfForallMemIntegers C F' hB
  have := P.isScalarTower_integersOfForallMem_extension (F' := F') hB
  exact .of_algebraMap_eq fun x ↦ Subtype.ext (IsScalarTower.algebraMap_apply B C F' x)

end Tower

end IntegralClosure

end TauCeti.Place
