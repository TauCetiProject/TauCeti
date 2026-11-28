/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
public import TauCeti.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# The global dimension of a right rigid category without a pivotal structure

Let `C` be a preadditive right rigid monoidal category with finitely many isomorphism classes of
simple objects (`[Fintype (SimpleClasses C)]`). Given a family of isomorphisms
`a : ∀ S : SimpleClasses C, S.repr ≅ S.reprᘁᘁ` identifying each chosen simple representative with
its double right dual, its *global dimension* is the scalar

`normGlobalDim C a := ∑ S : SimpleClasses C, squaredNorm (a S) : 𝟙_ C ⟶ 𝟙_ C`.

In a finite semisimple rigid category with simple tensor unit, such a family exists by
`TauCeti.nonempty_iso_rightDual_rightDual`. Whenever each simple representative has scalar
endomorphisms over a commutative semiring `R` (`Function.Surjective (algebraMap R (End S.repr))`),
`TauCeti.squaredNorm_congr` makes every summand—and hence `normGlobalDim C a`—independent of the
chosen family `a` (`TauCeti.normGlobalDim_congr_of_surjective`), and in particular over an
algebraically closed field when the simple endomorphism spaces are finite-dimensional
(`TauCeti.normGlobalDim_congr`). When `C` also carries a pivotal structure,
`TauCeti.normGlobalDim_eq_globalDim` in `TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim`
identifies `normGlobalDim C a` with the pivotal `TauCeti.globalDim C`.

## Main declarations

* `TauCeti.normGlobalDim` and `TauCeti.normGlobalDim_def`: the global dimension of `C` formed from
  squared norms of simple representatives;
* `TauCeti.normGlobalDim_congr_of_surjective` and `TauCeti.normGlobalDim_congr`: independence of
  `TauCeti.normGlobalDim` from the chosen family of double-dual isomorphisms.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  [arXiv:math/0203060](https://arxiv.org/abs/math/0203060), §2.1, Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21,
  Definition 7.21.3
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]

/-- **The global dimension without a pivotal structure** (Etingof–Nikshych–Ostrik, Definition 2.2;
Etingof–Gelaki–Nikshych–Ostrik, Definition 7.21.3): the sum of the squared norms of the simple
representatives, for a family of isomorphisms to their double right duals. When the simple
representatives have scalar endomorphisms, its value is independent of the family `a` by
`TauCeti.normGlobalDim_congr_of_surjective`. -/
noncomputable def normGlobalDim (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, squaredNorm (a S)

/-- The defining formula of `TauCeti.normGlobalDim`. -/
theorem normGlobalDim_def (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) :=
  (rfl)

/-- When every simple representative has scalar endomorphisms over a commutative semiring `R`,
`TauCeti.normGlobalDim` is independent of the chosen double-dual isomorphisms. -/
theorem normGlobalDim_congr_of_surjective (R : Type w) [CommSemiring R] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Surjective (algebraMap R (End S.repr)))
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  Finset.sum_congr rfl fun S _ ↦ squaredNorm_congr R (hS S) (a S) (b S)

/-- Over an algebraically closed field `k`, if each simple representative has finite-dimensional
endomorphisms, `TauCeti.normGlobalDim` is independent of the chosen double-dual isomorphisms. -/
theorem normGlobalDim_congr (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C]
    [Linear k C] [MonoidalLinear k C] [HasKernels C]
    [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  normGlobalDim_congr_of_surjective C k
    (fun S ↦ (bijective_algebraMap_end_of_simple k S.repr).surjective) a b

end TauCeti
