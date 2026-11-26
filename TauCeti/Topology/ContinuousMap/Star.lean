/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.Path

/-!
# Nonunital star-algebra homomorphisms on spaces of continuous maps

`Mathlib.Topology.ContinuousMap.Star` equips `C(X, A)` with its pointwise star-ring and
star-module structures and bundles evaluation, precomposition, and postcomposition as unital
`StarAlgHom`s. For possibly nonunital topological star-algebras — such as nonunital C⋆-algebras
and path algebras `C([0, 1], B)` — this file provides the corresponding `NonUnitalStarAlgHom`
bundlings, together with the matching-endpoint nonunital star-subalgebra and path-concatenation
homomorphism on `C(unitInterval, A)`.

## Main definitions

* `ContinuousMap.evalNonUnitalStarAlgHom`: evaluation `C(X, A) →⋆ₙₐ[R] A` at a point `x : X`.
* `ContinuousMap.constNonUnitalStarAlgHom`: constant-map inclusion `A →⋆ₙₐ[R] C(X, A)`.
* `ContinuousMap.compNonUnitalStarAlgHom'`: precomposition `C(Y, A) →⋆ₙₐ[R] C(X, A)` along a
  continuous map `f : C(X, Y)`.
* `ContinuousMap.compNonUnitalStarAlgHom`: postcomposition `C(X, A) →⋆ₙₐ[R] C(X, B)` along a
  continuous nonunital star-algebra homomorphism `g : A →⋆ₙₐ[R] B`.
* `ContinuousMap.pathConcatSubalgebra` and `ContinuousMap.pathConcatNonUnitalStarAlgHom`: the
  nonunital `⋆`-subalgebra `{(f, g) ∈ C(I, A) × C(I, A) | f 1 = g 0}` (closed when `A` is `T₂`)
  and path concatenation `pathConcatSubalgebra R A →⋆ₙₐ[R] C(unitInterval, A)` at `s = 1 / 2`.
-/

public section

namespace ContinuousMap

section NonUnitalStarAlgHom

variable (R : Type*) {X Y : Type*} (A B : Type*) [Semiring R]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
  [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [Star A] [ContinuousStar A]
  [Module R A] [ContinuousConstSMul R A]
  [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B] [Star B] [ContinuousStar B]
  [Module R B] [ContinuousConstSMul R B]

/-- Pointwise evaluation `C(X, A) →⋆ₙₐ[R] A` at `x : X` as a nonunital `⋆`-algebra homomorphism. -/
def evalNonUnitalStarAlgHom (x : X) : C(X, A) →⋆ₙₐ[R] A :=
  { toFun := fun f ↦ f x, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem evalNonUnitalStarAlgHom_apply (x : X) (f : C(X, A)) :
    evalNonUnitalStarAlgHom R A x f = f x := (rfl)

variable (X) in
/-- Constant-map inclusion `A →⋆ₙₐ[R] C(X, A)` as a nonunital `⋆`-algebra homomorphism. -/
def constNonUnitalStarAlgHom : A →⋆ₙₐ[R] C(X, A) :=
  { toFun := ContinuousMap.const X, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem constNonUnitalStarAlgHom_apply (a : A) (x : X) :
    constNonUnitalStarAlgHom R X A a x = a := (rfl)

/-- Precomposition `C(Y, A) →⋆ₙₐ[R] C(X, A)` along `f : C(X, Y)` as a nonunital `⋆`-algebra
homomorphism. -/
def compNonUnitalStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₙₐ[R] C(X, A) :=
  { toFun := fun g ↦ g.comp f, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem compNonUnitalStarAlgHom'_apply (f : C(X, Y)) (g : C(Y, A)) (x : X) :
    compNonUnitalStarAlgHom' R A f g x = g (f x) := (rfl)

/-- Postcomposition `C(X, A) →⋆ₙₐ[R] C(X, B)` along a continuous nonunital `⋆`-algebra homomorphism.
-/
def compNonUnitalStarAlgHom (g : A →⋆ₙₐ[R] B) (hg : Continuous g) :
    C(X, A) →⋆ₙₐ[R] C(X, B) where
  toFun f := ⟨g ∘ f, hg.comp f.continuous⟩
  map_smul' c f := by ext x; exact map_smul g c (f x)
  map_zero' := by ext _; exact map_zero g
  map_add' f₁ f₂ := by ext x; exact map_add g (f₁ x) (f₂ x)
  map_mul' f₁ f₂ := by ext x; exact map_mul g (f₁ x) (f₂ x)
  map_star' f := by ext x; exact map_star g (f x)

@[simp]
theorem compNonUnitalStarAlgHom_apply (g : A →⋆ₙₐ[R] B) (hg : Continuous g)
    (f : C(X, A)) (x : X) : compNonUnitalStarAlgHom R A B g hg f x = g (f x) := (rfl)

end NonUnitalStarAlgHom

section PathConcat

open unitInterval

variable (R A : Type*) [CommSemiring R] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [Star A] [ContinuousStar A]
  [Module R A] [ContinuousConstSMul R A]

/-- The nonunital `⋆`-subalgebra of pairs `(f, g) ∈ C(unitInterval, A) × C(unitInterval, A)`
matching at `f 1 = g 0`, the domain of path concatenation. -/
def pathConcatSubalgebra :
    NonUnitalStarSubalgebra R (C(unitInterval, A) × C(unitInterval, A)) where
  carrier := {p | p.1 1 = p.2 0}
  mul_mem' {_ _} hp hq := by rw [Set.mem_ofPred_eq] at hp hq ⊢; simp [hp, hq]
  add_mem' {_ _} hp hq := by rw [Set.mem_ofPred_eq] at hp hq ⊢; simp [hp, hq]
  zero_mem' := rfl
  smul_mem' _ {_} hp := by rw [Set.mem_ofPred_eq] at hp ⊢; simp [hp]
  star_mem' {_} hp := by rw [Set.mem_ofPred_eq] at hp ⊢; simp [hp]

/-- A pair `(f, g)` belongs to `pathConcatSubalgebra R A` if and only if `f 1 = g 0`. -/
@[simp, grind =]
theorem mem_pathConcatSubalgebra {R A : Type*} [CommSemiring R] [TopologicalSpace A]
    [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [Star A] [ContinuousStar A]
    [Module R A] [ContinuousConstSMul R A] {p : C(unitInterval, A) × C(unitInterval, A)} :
    p ∈ pathConcatSubalgebra R A ↔ p.1 1 = p.2 0 :=
  Iff.rfl

/-- The underlying set of `pathConcatSubalgebra R A` is `{p | p.1 1 = p.2 0}`. -/
@[simp, norm_cast]
theorem coe_pathConcatSubalgebra :
    (pathConcatSubalgebra R A : Set (C(unitInterval, A) × C(unitInterval, A))) =
      {p | p.1 1 = p.2 0} :=
  (rfl)

/-- For a Hausdorff target `A`, `pathConcatSubalgebra R A` is closed in
`C(unitInterval, A) × C(unitInterval, A)`. -/
instance isClosed_pathConcatSubalgebra [T2Space A] :
    IsClosed (pathConcatSubalgebra R A : Set (C(unitInterval, A) × C(unitInterval, A))) :=
  isClosed_eq ((continuous_eval_const (1 : unitInterval)).comp continuous_fst)
    ((continuous_eval_const (0 : unitInterval)).comp continuous_snd)

/-- Path concatenation at `s = 1 / 2` as a nonunital `⋆`-algebra homomorphism out of
`pathConcatSubalgebra R A`. -/
noncomputable def pathConcatNonUnitalStarAlgHom :
    pathConcatSubalgebra R A →⋆ₙₐ[R] C(unitInterval, A) where
  toFun p :=
    ((Path.mk p.val.1 rfl rfl).trans
      (Path.mk p.val.2 (mem_pathConcatSubalgebra.mp p.property).symm rfl)).toContinuousMap
  map_smul' _ _ := by
    ext; simp only [smul_apply, toFun_eq_coe, Path.coe_toContinuousMap, Path.trans_apply,
      Path.coe_mk']
    split_ifs <;> simp
  map_zero' := by
    ext; simp only [zero_apply, toFun_eq_coe, Path.coe_toContinuousMap, Path.trans_apply,
      Path.coe_mk']
    split_ifs <;> simp
  map_add' _ _ := by
    ext; simp only [add_apply, toFun_eq_coe, Path.coe_toContinuousMap, Path.trans_apply,
      Path.coe_mk']
    split_ifs <;> simp
  map_mul' _ _ := by
    ext; simp only [mul_apply, toFun_eq_coe, Path.coe_toContinuousMap, Path.trans_apply,
      Path.coe_mk']
    split_ifs <;> simp
  map_star' _ := by
    ext; simp only [star_apply, toFun_eq_coe, Path.coe_toContinuousMap, Path.trans_apply,
      Path.coe_mk']
    split_ifs <;> simp

/-- Pointwise evaluation of `pathConcatNonUnitalStarAlgHom` is given by `Path.trans`. -/
@[simp]
theorem pathConcatNonUnitalStarAlgHom_apply (p : pathConcatSubalgebra R A) (s : unitInterval) :
    pathConcatNonUnitalStarAlgHom R A p s =
      ((Path.mk p.val.1 rfl rfl).trans
        (Path.mk p.val.2 (mem_pathConcatSubalgebra.mp p.property).symm rfl)) s :=
  (rfl)

end PathConcat

end ContinuousMap
