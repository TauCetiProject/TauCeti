/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
public import TauCeti.CategoryTheory.Semisimple.Rigid

/-!
# The global dimension of a rigid category without a pivotal structure

Let `C` be a preadditive right rigid monoidal category with finitely many isomorphism classes of
simple objects (`[Fintype (SimpleClasses C)]`). Given a family
`a : ∀ S : SimpleClasses C, S.repr ≅ (S.repr)ᘁᘁ` of isomorphisms from the chosen simple
representatives to their double right duals, Etingof–Nikshych–Ostrik define the **global
dimension** of `C` as the sum of their squared norms:

`normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) : 𝟙_ C ⟶ 𝟙_ C`.

No pivotal structure is needed: `a` is an arbitrary family of objectwise isomorphisms, with no
monoidality or naturality condition. When the simple representatives have scalar endomorphisms over
a commutative semiring `R`—and in particular over an algebraically closed field `k` when their
endomorphism spaces are finite-dimensional—`TauCeti.squaredNorm_congr` shows that each summand is
independent of `a S`, so `normGlobalDim C a` is independent of `a` (`TauCeti.normGlobalDim_congr`,
`TauCeti.normGlobalDim_congr_of_simple`). Moreover, in a finite semisimple rigid category with
simple tensor unit, such a family `a` always exists
(`TauCeti.nonempty_forall_iso_rightDual_rightDual`), by `TauCeti.nonempty_iso_rightDual_rightDual`.

## Main declarations

* `TauCeti.normGlobalDim`: the global dimension `∑ S, squaredNorm (a S)` of a preadditive right
  rigid category for a family `a` of bidual isomorphisms on simple representatives;
* `TauCeti.normGlobalDim_congr` and `TauCeti.normGlobalDim_congr_of_simple`: independence of the
  chosen family `a` when simple representatives have scalar endomorphisms;
* `TauCeti.nonempty_forall_iso_rightDual_rightDual`: existence of a family
  `∀ S : SimpleClasses C, S.repr ≅ (S.repr)ᘁᘁ` in a finite semisimple rigid category with simple
  tensor unit.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Definition 7.21.3
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

section RightRigid

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]

/-- **The global dimension without a pivotal structure** (Etingof–Nikshych–Ostrik, *On fusion
categories*, Definition 2.2): the sum over `S : SimpleClasses C` of `squaredNorm (a S)` for a
family `a` of isomorphisms from the simple representatives to their double right duals. -/
noncomputable def normGlobalDim (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, squaredNorm (a S)

/-- The defining formula of `TauCeti.normGlobalDim`. -/
theorem normGlobalDim_def (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) :=
  (rfl)

variable {C}

/-- **Independence of the family of bidual isomorphisms**: when each simple representative has
scalar endomorphisms over a commutative semiring `R`, `normGlobalDim C a` does not depend on `a`. -/
theorem normGlobalDim_congr (R : Type w) [CommSemiring R] [MonoidalPreadditive C] [Linear R C]
    [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  Finset.sum_congr rfl fun S _ ↦ squaredNorm_congr R (hS S) (a S) (b S)

/-- Over an algebraically closed field `k`, if each simple representative has finite-dimensional
endomorphisms, `normGlobalDim C a` does not depend on the chosen family `a`. -/
theorem normGlobalDim_congr_of_simple (k : Type w) [Field k] [IsAlgClosed k]
    [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [HasKernels C]
    [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  normGlobalDim_congr k (fun S ↦ bijective_algebraMap_end_of_simple k S.repr) a b

end RightRigid

/-- In a finite semisimple rigid category with simple tensor unit, there exists a family of
isomorphisms `∀ S : SimpleClasses C, S.repr ≅ (S.repr)ᘁᘁ`. -/
theorem nonempty_forall_iso_rightDual_rightDual (C : Type u) [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C]
    [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] :
    Nonempty (∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :=
  ⟨fun S ↦ Classical.choice (nonempty_iso_rightDual_rightDual S.repr)⟩

end TauCeti
