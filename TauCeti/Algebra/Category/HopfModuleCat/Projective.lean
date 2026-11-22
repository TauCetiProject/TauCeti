/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.HopfModuleCat.Monoidal
public import TauCeti.Algebra.HopfAlgebra.Frobenius
public import TauCeti.Algebra.HopfAlgebra.Module.Projective
public import TauCeti.CategoryTheory.Exact.Stable.Basic
import Mathlib.RingTheory.Finiteness.Small

/-!
# Projective modules form a tensor ideal

Let `H` be a Hopf algebra over a field `k`, small in the universe of `k`. In the monoidal category
`HopfModuleCat k H` of all left `H`-modules, `P ⊗ M` is projective whenever `P` is projective
(`TauCeti.HopfModuleCat.projective_tensor_left`). If the antipode is bijective, then `M ⊗ P` is
projective as well (`TauCeti.HopfModuleCat.projective_tensor_right`); this holds in particular for
every finite-dimensional Hopf algebra, by the Larson–Sweedler theorem `TauCeti.antipode_bijective`.

Consequently, the morphisms factoring through a projective module form a two-sided tensor ideal:
the projective stable ideal of the abelian exact structure is closed under whiskering on either
side (`TauCeti.HopfModuleCat.whiskerRight_mem_projectiveStableIdeal` and
`TauCeti.HopfModuleCat.whiskerLeft_mem_projectiveStableIdeal`). This is what lets the tensor
product descend to the stable module category.

The module-theoretic statements, over any commutative semiring, are
`TauCeti.BialgebraModule.projective_tensor_left` and
`TauCeti.BialgebraModule.projective_tensor_right`.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.HopfModuleCat

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]

section Small

variable [Small.{u} H]

/-- In `HopfModuleCat k H`, the tensor product `P ⊗ M` of a projective module `P` with any module
`M` is projective. -/
instance projective_tensor_left (P M : HopfModuleCat k H) [Projective P] : Projective (P ⊗ M) := by
  have : Module.Projective H P := ModuleCat.projective_of_module_projective (P : ModuleCat.{u} H)
  have := BialgebraModule.projective_tensor_left (R := k) (H := H) (P := P) (M := M)
  exact ModuleCat.projective_of_categoryTheory_projective
    ((P ⊗ M : HopfModuleCat k H) : ModuleCat.{u} H)

/-- In `HopfModuleCat k H`, if the antipode of `H` is bijective, the tensor product `M ⊗ P` of any
module `M` with a projective module `P` is projective. -/
theorem projective_tensor_right (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H))
    (M P : HopfModuleCat k H) [Projective P] : Projective (M ⊗ P) := by
  have : Module.Projective H P := ModuleCat.projective_of_module_projective (P : ModuleCat.{u} H)
  have := BialgebraModule.projective_tensor_right (M := M) (P := P) hS
  exact ModuleCat.projective_of_categoryTheory_projective
    ((M ⊗ P : HopfModuleCat k H) : ModuleCat.{u} H)

/-- Right whiskering preserves morphisms that factor through a projective module. -/
theorem whiskerRight_mem_projectiveStableIdeal {X Y : HopfModuleCat k H} {f : X ⟶ Y}
    (hf : f ∈ (ExactStructure.abelian (HopfModuleCat k H)).projectiveStableIdeal.hom X Y)
    (M : HopfModuleCat k H) :
    f ▷ M ∈
      (ExactStructure.abelian (HopfModuleCat k H)).projectiveStableIdeal.hom (X ⊗ M) (Y ⊗ M) := by
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at hf ⊢
  obtain ⟨Q, hQ, i, p, rfl⟩ := hf
  have := (ExactStructure.abelian_isProjective_iff Q).mp hQ
  exact ⟨Q ⊗ M, (ExactStructure.abelian_isProjective_iff _).mpr inferInstance, i ▷ M, p ▷ M,
    comp_whiskerRight i p M⟩

/-- If the antipode of `H` is bijective, left whiskering preserves morphisms that factor through a
projective module. -/
theorem whiskerLeft_mem_projectiveStableIdeal
    (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H)) {X Y : HopfModuleCat k H}
    {f : X ⟶ Y}
    (hf : f ∈ (ExactStructure.abelian (HopfModuleCat k H)).projectiveStableIdeal.hom X Y)
    (M : HopfModuleCat k H) :
    M ◁ f ∈
      (ExactStructure.abelian (HopfModuleCat k H)).projectiveStableIdeal.hom (M ⊗ X) (M ⊗ Y) := by
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at hf ⊢
  obtain ⟨Q, hQ, i, p, rfl⟩ := hf
  have := (ExactStructure.abelian_isProjective_iff Q).mp hQ
  exact ⟨M ⊗ Q, (ExactStructure.abelian_isProjective_iff _).mpr (projective_tensor_right hS M Q),
    M ◁ i, M ◁ p, whiskerLeft_comp M i p⟩

end Small

/-- Over a finite-dimensional Hopf algebra, the tensor product `M ⊗ P` of any module `M` with a
projective module `P` is projective. -/
instance projective_tensor_right_of_finiteDimensional [FiniteDimensional k H]
    (M P : HopfModuleCat k H) [Projective P] : Projective (M ⊗ P) := by
  have := Module.Finite.small k H
  exact projective_tensor_right (antipode_bijective k H) M P

end TauCeti.HopfModuleCat
