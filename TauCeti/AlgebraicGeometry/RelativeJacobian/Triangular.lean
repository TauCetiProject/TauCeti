/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The triangular isomorphism of fibre powers of a group object

Let `A` be a group object in a cartesian monoidal category `C` (for instance a group scheme over
`S`, a group object of `Over S`) and `n` a natural number. On the fibre power `A^{n+1}`, the product
`∏ᶜ (fun _ : Fin (n + 1) ↦ A)` with projections `p₀, …, pₙ`, the **triangular coordinate change**
`R` has first projection `p₀` and remaining projections `p_r p₀⁻¹`
(`TauCeti.RelativeJacobian.triangularForward`); its inverse has first projection `p₀` and
remaining projections `p_r p₀` (`TauCeti.RelativeJacobian.triangularInverse`). Multiplication is
that of the group `Hom(T, A)` of `T`-valued points (`CategoryTheory.Hom.group`); no commutativity
is used, and the head `p₀` stands on the right in both maps.

On `T`-valued points, that is on tuples `q : Fin (n + 1) → (T ⟶ A)`, the two maps are the
coordinate operations `q ↦ (q₀, q₁ q₀⁻¹, …, qₙ q₀⁻¹)` and `r ↦ (r₀, r₁ r₀, …, rₙ r₀)` of
`TauCeti.RelativeJacobian.triangularEquiv`, which make sense in any group. The two maps commute with
every monoidal functor that preserves the fibre power, through the canonical comparison
`PreservesProduct.iso` (`TauCeti.RelativeJacobian.triangularForward_comp_iso_hom`); for schemes,
with base change along any `S' ⟶ S` (`TauCeti.RelativeJacobian.triangularBaseChange`), including
nonreduced bases.

This is JacobianChallengePartII §5.5, the coordinate change used in the proof of Yuan's Theorem
4.17(5).

## Main definitions

* `TauCeti.RelativeJacobian.triangularEquiv`: the coordinate operations on tuples in a group.
* `TauCeti.RelativeJacobian.triangularForward` and `TauCeti.RelativeJacobian.triangularInverse`:
  the two morphisms of the fibre power.
* `TauCeti.RelativeJacobian.triangularIsomorphism`: the isomorphism with these two directions.

## Main results

* `TauCeti.RelativeJacobian.triangularForward_π_zero`, `triangularForward_π_succ`,
  `triangularInverse_π_zero`, `triangularInverse_π_succ`: the projections.
* `TauCeti.RelativeJacobian.triangularForward_comp_triangularInverse` and
  `triangularInverse_comp_triangularForward`: the two composites are identities.
* `TauCeti.RelativeJacobian.comp_triangularForward_π` and `comp_triangularInverse_π`: on
  represented points, the two maps are the coordinate operations.
* `TauCeti.RelativeJacobian.triangularForward_comp_iso_hom` and
  `TauCeti.RelativeJacobian.iso_inv_comp_triangularInverse`: compatibility with monoidal functors
  preserving the fibre power; `TauCeti.RelativeJacobian.triangularBaseChange` is the case of base
  change of group schemes.

## References

* Yuan, [arXiv:2108.05625v4](https://arxiv.org/pdf/2108.05625v4), proof of Theorem 4.17(5),
  p. 98 (the reference of JacobianChallengePartII §5.5).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.RelativeJacobian

universe v u

/-! ### The coordinate operations in a group -/

section Group

variable {G : Type*} [Group G] {n : ℕ}

/-- **The triangular coordinate change on tuples in a group**: `q ↦ (q₀, q₁ q₀⁻¹, …, qₙ q₀⁻¹)`, with
inverse `r ↦ (r₀, r₁ r₀, …, rₙ r₀)`. -/
def triangularEquiv (n : ℕ) : (Fin (n + 1) → G) ≃ (Fin (n + 1) → G) where
  toFun q := Fin.cases (q 0) fun r ↦ q r.succ / q 0
  invFun q := Fin.cases (q 0) fun r ↦ q r.succ * q 0
  left_inv q := by
    ext j
    refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp
  right_inv q := by
    ext j
    refine Fin.cases ?_ (fun r ↦ ?_) j <;> simp

@[simp]
theorem triangularEquiv_apply_zero (q : Fin (n + 1) → G) : triangularEquiv n q 0 = q 0 :=
  (rfl)

@[simp]
theorem triangularEquiv_apply_succ (q : Fin (n + 1) → G) (r : Fin n) :
    triangularEquiv n q r.succ = q r.succ / q 0 :=
  (rfl)

@[simp]
theorem triangularEquiv_symm_apply_zero (q : Fin (n + 1) → G) :
    (triangularEquiv n).symm q 0 = q 0 :=
  (rfl)

@[simp]
theorem triangularEquiv_symm_apply_succ (q : Fin (n + 1) → G) (r : Fin n) :
    (triangularEquiv n).symm q r.succ = q r.succ * q 0 :=
  (rfl)

end Group

/-! ### The triangular isomorphism of a fibre power -/

section Fibre

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (A : C) [GrpObj A] (n : ℕ)
  [HasProduct fun _ : Fin (n + 1) ↦ A]

/-- **The forward triangular morphism** of the fibre power `A^{n+1}`: first projection `p₀`,
remaining projections `p_r p₀⁻¹`. -/
def triangularForward : (∏ᶜ fun _ : Fin (n + 1) ↦ A) ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ A :=
  Pi.lift fun j ↦ triangularEquiv n (fun i ↦ Pi.π (fun _ : Fin (n + 1) ↦ A) i) j

/-- **The inverse triangular morphism** of the fibre power `A^{n+1}`: first projection `p₀`,
remaining projections `p_r p₀`. -/
def triangularInverse : (∏ᶜ fun _ : Fin (n + 1) ↦ A) ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ A :=
  Pi.lift fun j ↦ (triangularEquiv n).symm (fun i ↦ Pi.π (fun _ : Fin (n + 1) ↦ A) i) j

variable {A n}

/-- On represented points, the forward triangular morphism is the coordinate operation
`q ↦ (q₀, q₁ q₀⁻¹, …, qₙ q₀⁻¹)`. -/
theorem comp_triangularForward_π {T : C} (q : T ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ A)
    (j : Fin (n + 1)) :
    q ≫ triangularForward A n ≫ Pi.π _ j =
      triangularEquiv n (fun i ↦ q ≫ Pi.π (fun _ : Fin (n + 1) ↦ A) i) j := by
  rw [triangularForward, Pi.lift_comp_π]
  refine Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [GrpObj.comp_div]

/-- On represented points, the inverse triangular morphism is the coordinate operation
`r ↦ (r₀, r₁ r₀, …, rₙ r₀)`. -/
theorem comp_triangularInverse_π {T : C} (q : T ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ A)
    (j : Fin (n + 1)) :
    q ≫ triangularInverse A n ≫ Pi.π _ j =
      (triangularEquiv n).symm (fun i ↦ q ≫ Pi.π (fun _ : Fin (n + 1) ↦ A) i) j := by
  rw [triangularInverse, Pi.lift_comp_π]
  refine Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem triangularForward_π_zero :
    triangularForward A n ≫ Pi.π _ 0 = Pi.π (fun _ : Fin (n + 1) ↦ A) 0 := by
  simpa using comp_triangularForward_π (𝟙 _) 0

@[reassoc (attr := simp)]
theorem triangularForward_π_succ (r : Fin n) :
    triangularForward A n ≫ Pi.π _ r.succ =
      Pi.π (fun _ : Fin (n + 1) ↦ A) r.succ / Pi.π (fun _ : Fin (n + 1) ↦ A) 0 := by
  simpa using comp_triangularForward_π (𝟙 _) r.succ

@[reassoc (attr := simp)]
theorem triangularInverse_π_zero :
    triangularInverse A n ≫ Pi.π _ 0 = Pi.π (fun _ : Fin (n + 1) ↦ A) 0 := by
  simpa using comp_triangularInverse_π (𝟙 _) 0

@[reassoc (attr := simp)]
theorem triangularInverse_π_succ (r : Fin n) :
    triangularInverse A n ≫ Pi.π _ r.succ =
      Pi.π (fun _ : Fin (n + 1) ↦ A) r.succ * Pi.π (fun _ : Fin (n + 1) ↦ A) 0 := by
  simpa using comp_triangularInverse_π (𝟙 _) r.succ

@[reassoc (attr := simp)]
theorem triangularForward_comp_triangularInverse :
    triangularForward A n ≫ triangularInverse A n = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun j ↦ Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem triangularInverse_comp_triangularForward :
    triangularInverse A n ≫ triangularForward A n = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun j ↦ Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [GrpObj.comp_div]

variable (A n) in
/-- **The triangular isomorphism** of the fibre power `A^{n+1}`, with forward map
`triangularForward A n` and inverse `triangularInverse A n`. -/
def triangularIsomorphism : (∏ᶜ fun _ : Fin (n + 1) ↦ A) ≅ ∏ᶜ fun _ : Fin (n + 1) ↦ A where
  hom := triangularForward A n
  inv := triangularInverse A n

@[simp]
theorem triangularIsomorphism_hom : (triangularIsomorphism A n).hom = triangularForward A n :=
  (rfl)

@[simp]
theorem triangularIsomorphism_inv : (triangularIsomorphism A n).inv = triangularInverse A n :=
  (rfl)

/-- For `n = 0` the triangular isomorphism is the identity of the one-factor fibre power. -/
theorem triangularForward_zero [HasProduct fun _ : Fin 1 ↦ A] : triangularForward A 0 = 𝟙 _ :=
  Pi.hom_ext _ _ fun j ↦ by
    rw [Fin.eq_zero j, triangularForward_π_zero, Category.id_comp]

/-- For `n = 0` the inverse triangular morphism is the identity. -/
theorem triangularInverse_zero [HasProduct fun _ : Fin 1 ↦ A] : triangularInverse A 0 = 𝟙 _ :=
  Pi.hom_ext _ _ fun j ↦ by
    rw [Fin.eq_zero j, triangularInverse_π_zero, Category.id_comp]

end Fibre

/-! ### Compatibility with monoidal functors and base change -/

section Functor

open scoped CategoryTheory.Obj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {D : Type*} [Category* D]
  [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (A : C) [GrpObj A] (n : ℕ)
  [HasProduct fun _ : Fin (n + 1) ↦ A] [HasProduct fun _ : Fin (n + 1) ↦ F.obj A]
  [PreservesLimit (Discrete.functor fun _ : Fin (n + 1) ↦ A) F]

/-- **Compatibility with monoidal functors.** A monoidal functor `F` preserving the fibre power
carries the forward triangular morphism of `A` to that of `F A`, through the canonical comparison
`F (A^{n+1}) ≅ (F A)^{n+1}`. -/
@[reassoc]
theorem triangularForward_comp_iso_hom :
    F.map (triangularForward A n) ≫ (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).hom ≫ triangularForward (F.obj A) n := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, Category.assoc, comp_triangularForward_π]
  simp only [PreservesProduct.iso_hom, piComparison_comp_π, ← Functor.map_comp]
  refine Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [div_eq_mul_inv, Functor.map_mul, Functor.map_inv']

/-- **Compatibility with monoidal functors**, for the inverse triangular morphism. -/
@[reassoc]
theorem triangularInverse_comp_iso_hom :
    F.map (triangularInverse A n) ≫ (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).hom ≫ triangularInverse (F.obj A) n := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, Category.assoc, comp_triangularInverse_π]
  simp only [PreservesProduct.iso_hom, piComparison_comp_π, ← Functor.map_comp]
  refine Fin.cases ?_ (fun r ↦ ?_) j
  · simp
  · simp [Functor.map_mul]

/-- The compatibility for the inverse morphism, read through the inverse comparison:
`C⁻¹ ≫ F (R⁻¹) = R'⁻¹ ≫ C⁻¹`. -/
@[reassoc]
theorem iso_inv_comp_triangularInverse :
    (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).inv ≫ F.map (triangularInverse A n) =
      triangularInverse (F.obj A) n ≫ (PreservesProduct.iso F fun _ : Fin (n + 1) ↦ A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← triangularInverse_comp_iso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end Functor

section Scheme

open AlgebraicGeometry

open scoped CategoryTheory.Obj

variable {S S' : Scheme.{u}} (f : S' ⟶ S) (A : Over S) [GrpObj A] (n : ℕ)

/-- **The triangular coordinate change commutes with base change.** For a group scheme `A` over
`S`, viewed as a group object of `Over S`, and any morphism `f : S' ⟶ S`, base change along `f`
carries both triangular morphisms of `A^{n+1}_S` to those of the base change of `A`, through the
canonical comparison of fibre powers. -/
theorem triangularBaseChange :
    (Over.pullback f).map (triangularForward A n) ≫
        (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom ≫
        triangularForward ((Over.pullback f).obj A) n ∧
    (Over.pullback f).map (triangularInverse A n) ≫
        (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom =
      (PreservesProduct.iso (Over.pullback f) fun _ : Fin (n + 1) ↦ A).hom ≫
        triangularInverse ((Over.pullback f).obj A) n :=
  ⟨triangularForward_comp_iso_hom _ _ _, triangularInverse_comp_iso_hom _ _ _⟩

end Scheme

end TauCeti.RelativeJacobian
