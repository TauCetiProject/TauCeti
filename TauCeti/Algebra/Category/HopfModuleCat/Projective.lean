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
public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.FactorThrough
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor

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
`TauCeti.BialgebraModule.projective_tensor_right`. Categorical projectivity in `ModuleCat` is
translated to module projectivity through Mathlib's `ModuleCat.projective_of_module_projective`,
which asks that `H` be small relative to the universe of `k`; this holds for finite-dimensional
`H`.

## Main declarations

* `TauCeti.HopfModuleCat.projective_tensorObj_left`,
  `TauCeti.HopfModuleCat.projective_tensorObj_right`: tensoring with a projective module on
  either side gives a projective module.
* `TauCeti.HopfModuleCat.projectiveIdeal`: the tensor ideal of morphisms factoring through a
  projective module.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
-/

public section

open CategoryTheory MonoidalCategory HopfAlgebra

universe u v

namespace TauCeti.HopfModuleCat

variable {k : Type u} [Field k] {H : Type v} [Ring H] [_root_.HopfAlgebra k H] [Small.{u} H]

/-- The tensor product `P ⊗ M` of a projective module `P` with any module `M` is projective. -/
instance projective_tensorObj_left (P M : HopfModuleCat k H) [Projective P] :
    Projective (P ⊗ M) := by
  have : Module.Projective H P := ModuleCat.projective_of_module_projective (R := H) P
  have := BialgebraModule.projective_tensor_left k H M P
  exact ModuleCat.projective_of_categoryTheory_projective (R := H)
    (ModuleCat.of H (BialgebraModule.Tensor k H P M))

/-- For a bijective antipode, the tensor product `M ⊗ P` of any module `M` with a projective
module `P` is projective. -/
theorem projective_tensorObj_right (hS : Function.Bijective (antipode k : H →ₗ[k] H))
    (M P : HopfModuleCat k H) [Projective P] : Projective (M ⊗ P) := by
  have : Module.Projective H P := ModuleCat.projective_of_module_projective (R := H) P
  have := BialgebraModule.projective_tensor_right k H M P hS
  exact ModuleCat.projective_of_categoryTheory_projective (R := H)
    (ModuleCat.of H (BialgebraModule.Tensor k H M P))

/-- For a bijective antipode, the morphisms factoring through a projective module form a tensor
ideal of the category of all modules. -/
def projectiveIdeal (hS : Function.Bijective (antipode k : H →ₗ[k] H)) :
    MonoidalIdeal (HopfModuleCat k H) where
  toMorphismIdeal := (isProjective (HopfModuleCat k H)).factorIdeal
  whiskerLeft_mem W {_ _} f hf := by
    have hle : (isProjective (HopfModuleCat k H)).factorIdeal ≤
        ((isProjective (HopfModuleCat k H)).factorIdeal).comap (tensorLeft W) :=
      ObjectProperty.factorIdeal_le_iff.2 fun {_ _ Z} hZ i p => by
        have : Projective Z := hZ
        rw [MorphismIdeal.mem_comap_hom, Functor.map_comp]
        exact ObjectProperty.comp_mem_factorIdeal (projective_tensorObj_right hS W Z) _ _
    exact (MorphismIdeal.mem_comap_hom _ _).1 (MorphismIdeal.le_def.1 hle f hf)
  whiskerRight_mem {_ _} f W hf := by
    have hle : (isProjective (HopfModuleCat k H)).factorIdeal ≤
        ((isProjective (HopfModuleCat k H)).factorIdeal).comap (tensorRight W) :=
      ObjectProperty.factorIdeal_le_iff.2 fun {_ _ Z} hZ i p => by
        have : Projective Z := hZ
        rw [MorphismIdeal.mem_comap_hom, Functor.map_comp]
        exact ObjectProperty.comp_mem_factorIdeal (projective_tensorObj_left Z W) _ _
    exact (MorphismIdeal.mem_comap_hom _ _).1 (MorphismIdeal.le_def.1 hle f hf)

/-- The underlying morphism ideal of `projectiveIdeal` is generated by the morphisms factoring
through a projective module. -/
@[simp]
theorem projectiveIdeal_toMorphismIdeal (hS : Function.Bijective (antipode k : H →ₗ[k] H)) :
    (projectiveIdeal hS).toMorphismIdeal = (isProjective (HopfModuleCat k H)).factorIdeal :=
  (rfl)

end TauCeti.HopfModuleCat
