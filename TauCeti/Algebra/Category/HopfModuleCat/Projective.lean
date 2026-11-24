/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Category.HopfModuleCat.Monoidal
public import TauCeti.Algebra.HopfAlgebra.Module.Projective
public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.FactorThrough
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projective modules form a tensor ideal

Let `H` be a Hopf algebra over a field `k`. In the monoidal category `HopfModuleCat k H` of all
left `H`-modules, with the tensor product over `k` on which `H` acts through its coproduct, the
tensor product `P ⊗ M` of a projective module `P` with any module `M` is projective. When the
antipode is bijective, as it is for a finite-dimensional Hopf algebra, `M ⊗ P` is projective as
well. Consequently the morphisms factoring through a projective module form a tensor ideal
(`TauCeti.HopfModuleCat.projectiveIdeal`), so the tensor product descends to the quotient of
`HopfModuleCat k H` by the maps factoring through projectives. For a finite-dimensional Hopf
algebra that quotient is the stable module category, on which the tensor product of modules
induces a monoidal structure.

The module-theoretic input is `TauCeti.BialgebraModule.projective_tensor_left` and
`TauCeti.BialgebraModule.projective_tensor_right`. Categorical projectivity in
`HopfModuleCat k H`, whose category structure is that of `ModuleCat H`, is translated to module
projectivity (`TauCeti.HopfModuleCat.projective_iff_module_projective`) through Mathlib's
comparison in `ModuleCat H`. A projective `H`-module is always a projective object; the converse
asks that `H` be small relative to the universe of `k`, which holds for finite-dimensional `H`.

## Main declarations

* `TauCeti.HopfModuleCat.projective_iff_module_projective`: an object is projective exactly when
  it is a projective `H`-module.
* `TauCeti.HopfModuleCat.projective_of_module_projective`: a projective `H`-module is a projective
  object, registered as an instance.
* `TauCeti.HopfModuleCat.projective_tensorObj_left`,
  `TauCeti.HopfModuleCat.projective_tensorObj_right`: tensoring with a projective module on
  either side gives a projective module.
* `TauCeti.HopfModuleCat.projectiveIdeal`: the tensor ideal of morphisms factoring through a
  projective module, whose members are exactly the morphisms factoring through a projective module
  (`TauCeti.HopfModuleCat.mem_projectiveIdeal_iff`).

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
-/

public section

open CategoryTheory MonoidalCategory HopfAlgebra

universe u v

namespace TauCeti.HopfModuleCat

variable {k : Type u} {H : Type v} [Ring H]

-- `HopfModuleCat k H` is `ModuleCat H` with the same category instance, so this is Mathlib's
-- comparison in `ModuleCat H` applied to the underlying object.
/-- A projective `H`-module is a projective object of `HopfModuleCat k H`. -/
instance projective_of_module_projective (M : HopfModuleCat k H) [Module.Projective H M] :
    Projective M :=
  ModuleCat.projective_of_categoryTheory_projective (R := H) M

variable [Small.{u} H]

-- As above, this is Mathlib's comparison in `ModuleCat H` applied to the underlying object.
/-- An object of `HopfModuleCat k H` is projective exactly when it is a projective `H`-module. -/
theorem projective_iff_module_projective (M : HopfModuleCat k H) :
    Projective M ↔ Module.Projective H M :=
  ⟨fun _ ↦ ModuleCat.projective_of_module_projective (R := H) M,
    fun _ ↦ ModuleCat.projective_of_categoryTheory_projective (R := H) M⟩

variable [Field k] [_root_.HopfAlgebra k H]

/-- The tensor product `P ⊗ M` of a projective module `P` with any module `M` is projective. -/
instance projective_tensorObj_left (P M : HopfModuleCat k H) [Projective P] :
    Projective (P ⊗ M) := by
  have := (projective_iff_module_projective P).1 ‹_›
  rw [tensorObj_def, projective_iff_module_projective]
  infer_instance

/-- For a bijective antipode, the tensor product `M ⊗ P` of any module `M` with a projective
module `P` is projective. -/
theorem projective_tensorObj_right (hS : Function.Bijective (antipode k : H →ₗ[k] H))
    (M P : HopfModuleCat k H) [Projective P] : Projective (M ⊗ P) := by
  have := (projective_iff_module_projective P).1 ‹_›
  rw [tensorObj_def, projective_iff_module_projective]
  exact BialgebraModule.projective_tensor_right k H M P hS

/-- For a bijective antipode, the morphisms factoring through a projective module form a tensor
ideal of the category of all modules. -/
noncomputable def projectiveIdeal (hS : Function.Bijective (antipode k : H →ₗ[k] H)) :
    MonoidalIdeal (HopfModuleCat k H) :=
  (isProjective (HopfModuleCat k H)).factorMonoidalIdeal
    (fun W Z (_ : Projective Z) ↦ projective_tensorObj_right hS W Z)
    (fun W Z (_ : Projective Z) ↦ projective_tensorObj_left Z W)

/-- The underlying morphism ideal of `projectiveIdeal` is generated by the morphisms factoring
through a projective module. -/
@[simp]
theorem projectiveIdeal_toMorphismIdeal (hS : Function.Bijective (antipode k : H →ₗ[k] H)) :
    (projectiveIdeal hS).toMorphismIdeal = (isProjective (HopfModuleCat k H)).factorIdeal :=
  ObjectProperty.factorMonoidalIdeal_toMorphismIdeal _ _ _

/-- A morphism lies in `projectiveIdeal` exactly when it factors through a projective module. -/
theorem mem_projectiveIdeal_iff (hS : Function.Bijective (antipode k : H →ₗ[k] H))
    {X Y : HopfModuleCat k H} (f : X ⟶ Y) :
    f ∈ (projectiveIdeal hS).toMorphismIdeal.hom X Y ↔ (isProjective _).FactorsThrough f := by
  simp

end TauCeti.HopfModuleCat
