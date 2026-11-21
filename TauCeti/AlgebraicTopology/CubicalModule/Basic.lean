/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fin.Parity
import TauCeti.Algebra.Category.ModuleCat.OfHom
import TauCeti.Data.Fin.FaceSwap

/-!
# Cubical modules and their cubical boundary complex

A *cubical module* over a ring `R` is a family of `R`-modules `X n`, one for each `n`, thought of
as the chains on `n`-dimensional cubes, with

* a face map `face i ε : X (n + 1) → X n` for each coordinate `i` and each endpoint `ε`, the
  restriction to the face where the `i`-th coordinate is `0` (`ε = false`) or `∞` (`ε = true`),
  and
* a degeneracy map `degen i : X n → X (n + 1)` for each coordinate `i`, the pullback along the
  projection forgetting the `i`-th coordinate,

satisfying the cubical identities. The basic example is the family of cycle groups on `Y × □ⁿ`,
`□ = ℙ¹ ∖ {1}`, meeting all faces properly, whose faces restrict to `xᵢ = 0, ∞` and whose
degeneracies pull back along the coordinate projections; this is the cubical model of Bloch's
higher Chow groups.

This file defines cubical modules, their morphisms and their (unnormalized) boundary complex,
with differential `∂ = ∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ^∞)` (coordinates numbered from `0`). Its
normalization is in `TauCeti.AlgebraicTopology.CubicalModule.Normalized`.

## Main definitions

* `TauCeti.CubicalModule`: a cubical object in `R`-modules.
* `TauCeti.CubicalModule.boundary`: the cubical boundary `∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ^∞)`.
* `TauCeti.CubicalModule.complex`: the cubical boundary complex.
* `TauCeti.CubicalModule.Hom`: morphisms of cubical modules, making them a category.
* `TauCeti.CubicalModule.complexFunctor`: the cubical boundary complex, as a functor.
* `TauCeti.CubicalModule.const`: the constant cubical module, all of whose faces and degeneracies
  are the identity.

## Main results

* `TauCeti.CubicalModule.boundary_comp_boundary`: `∂ ∘ ∂ = 0`.

## Implementation notes

The cubical identities are stated in the form used by `Fin.succAbove` and `Fin.predAbove`: deleting
the coordinates `i` and `i.succAbove j` of an `(n + 2)`-cube in either order gives the same face,
which is the single identity `TauCeti.CubicalModule.face_comp_face`, and similarly for the
degeneracies.

## References

* J. I. Burgos Gil and E. Feliu, *Higher arithmetic Chow groups*, Comment. Math. Helv. 87 (2012),
  521–587; arXiv:0907.5169, §1.6 and §2.1.
* M. Levine, *Bloch's higher Chow groups revisited*, Astérisque 226 (1994), 235–320.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti

/-- A **cubical module** over `R`: a family of `R`-modules `X n` of `n`-cubes, with face maps at
the two endpoints `0` (`false`) and `∞` (`true`) of each coordinate and with degeneracy maps,
satisfying the cubical identities. -/
structure CubicalModule (R : Type u) [Ring R] where
  /-- The module of `n`-cubes. -/
  X : ℕ → ModuleCat.{v} R
  /-- The face `face i ε : X (n + 1) → X n` in the `i`-th coordinate, at `0` for `ε = false` and
  at `∞` for `ε = true`. -/
  face {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : X (n + 1) →ₗ[R] X n
  /-- The degeneracy `degen i : X n → X (n + 1)` inserting a dummy `i`-th coordinate. -/
  degen {n : ℕ} (i : Fin (n + 1)) : X n →ₗ[R] X (n + 1)
  /-- Deleting the coordinates `i` and `i.succAbove j` in either order gives the same face. -/
  face_comp_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (ε η : Bool) :
    face j η ∘ₗ face i ε = face (j.predAbove i) ε ∘ₗ face (i.succAbove j) η
  /-- Restricting a degenerate cube to a face in its dummy coordinate recovers the cube. -/
  face_comp_degen_self {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : face i ε ∘ₗ degen i = .id
  /-- A face in a coordinate other than the dummy one commutes with the degeneracy. -/
  face_comp_degen {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1)) (ε : Bool) :
    face (j.succAbove i) ε ∘ₗ degen j = degen (i.predAbove j) ∘ₗ face i ε
  /-- Inserting dummy coordinates at `i` and `i.succAbove j` in either order agrees. -/
  degen_comp_degen {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    degen i ∘ₗ degen j = degen (i.succAbove j) ∘ₗ degen (j.predAbove i)

namespace CubicalModule

variable {R : Type u} [Ring R] (A : CubicalModule.{v} R)

theorem face_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (ε η : Bool) (x : A.X (n + 2)) :
    A.face j η (A.face i ε x) = A.face (j.predAbove i) ε (A.face (i.succAbove j) η x) :=
  congr($(A.face_comp_face i j ε η) x)

@[simp]
theorem face_degen_self {n : ℕ} (i : Fin (n + 1)) (ε : Bool) (x : A.X n) :
    A.face i ε (A.degen i x) = x :=
  congr($(A.face_comp_degen_self i ε) x)

theorem face_succAbove_degen {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1)) (ε : Bool)
    (x : A.X (n + 1)) :
    A.face (j.succAbove i) ε (A.degen j x) = A.degen (i.predAbove j) (A.face i ε x) :=
  congr($(A.face_comp_degen j i ε) x)

theorem degen_degen {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (x : A.X n) :
    A.degen i (A.degen j x) = A.degen (i.succAbove j) (A.degen (j.predAbove i) x) :=
  congr($(A.degen_comp_degen i j) x)

/-- The difference `∂ᵢ⁰ - ∂ᵢ^∞` of the two faces in the `i`-th coordinate. -/
def faceDiff {n : ℕ} (i : Fin (n + 1)) : A.X (n + 1) →ₗ[R] A.X n :=
  A.face i false - A.face i true

theorem faceDiff_apply {n : ℕ} (i : Fin (n + 1)) (x : A.X (n + 1)) :
    A.faceDiff i x = A.face i false x - A.face i true x :=
  (rfl)

/-- The face differences satisfy the semi-simplicial face identity. -/
theorem faceDiff_comp_faceDiff {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    A.faceDiff j ∘ₗ A.faceDiff i = A.faceDiff (j.predAbove i) ∘ₗ A.faceDiff (i.succAbove j) := by
  ext x
  simp only [LinearMap.comp_apply, faceDiff_apply, map_sub]
  rw [A.face_face i j false false, A.face_face i j false true, A.face_face i j true false,
    A.face_face i j true true]
  abel

/-- The **cubical boundary** `∂ = ∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ^∞) : X (n + 1) → X n`. -/
def boundary (n : ℕ) : A.X (n + 1) →ₗ[R] A.X n :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A.faceDiff i

theorem boundary_apply (n : ℕ) (x : A.X (n + 1)) :
    A.boundary n x = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A.faceDiff i x := by
  simp [boundary, LinearMap.sum_apply]

/-- The cubical boundary squares to zero. -/
theorem boundary_comp_boundary (n : ℕ) : A.boundary n ∘ₗ A.boundary (n + 1) = 0 := by
  -- The terms `(-1) ^ (i + j) ∂ⱼ ∂ᵢ` cancel in pairs under the involution `Fin.faceSwap`,
  -- by the face identity and the parity of the swapped exponent.
  ext x
  simp only [LinearMap.comp_apply, boundary_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    ← pow_add, LinearMap.zero_apply]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ ↦ Fin.faceSwap p) (fun p _ ↦ ?_)
    (fun p _ _ ↦ Fin.faceSwap_ne p) (fun _ _ ↦ by simp) (fun p _ ↦ Fin.faceSwap_faceSwap p)
  rw [Fin.faceSwap_def, ← LinearMap.comp_apply (A.faceDiff p.2), faceDiff_comp_faceDiff,
    LinearMap.comp_apply, Fin.neg_one_pow_succAbove_add_predAbove, neg_smul, add_neg_cancel]

@[simp]
theorem boundary_boundary (n : ℕ) (x : A.X (n + 2)) : A.boundary n (A.boundary (n + 1) x) = 0 :=
  congr($(A.boundary_comp_boundary n) x)

/-- The **cubical boundary complex** of a cubical module, with differential
`∂ = ∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ^∞)`. -/
@[expose] def complex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of A.X (fun n ↦ ModuleCat.ofHom (A.boundary n)) fun n ↦ by
    rw [← ModuleCat.ofHom_comp, A.boundary_comp_boundary]
    exact ModuleCat.ofHom_zero

@[simp]
theorem complex_X (n : ℕ) : A.complex.X n = A.X n :=
  (rfl)

theorem complex_d (n : ℕ) : A.complex.d (n + 1) n = ModuleCat.ofHom (A.boundary n) := by
  simp only [complex, ChainComplex.of_d]

@[simp]
theorem complex_d_apply (n : ℕ) (x : A.X (n + 1)) : A.complex.d (n + 1) n x = A.boundary n x := by
  rw [complex_d]
  -- The two sides differ only in the module instances on the carrier of `ModuleCat.of`.
  rfl

/-! ### Morphisms of cubical modules -/

/-- A **morphism of cubical modules**: linear maps of `n`-cubes, for all `n`, commuting with the
faces and the degeneracies. -/
@[ext]
structure Hom (A B : CubicalModule.{v} R) where
  /-- The linear map on `n`-cubes. -/
  f (n : ℕ) : A.X n →ₗ[R] B.X n
  /-- The maps commute with the faces. -/
  face_comp_f {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : B.face i ε ∘ₗ f (n + 1) = f n ∘ₗ A.face i ε
  /-- The maps commute with the degeneracies. -/
  degen_comp_f {n : ℕ} (i : Fin (n + 1)) : B.degen i ∘ₗ f n = f (n + 1) ∘ₗ A.degen i

instance : Category (CubicalModule.{v} R) where
  Hom := Hom
  id A := { f _ := .id, face_comp_f _ _ := rfl, degen_comp_f _ := rfl }
  comp φ ψ :=
    { f n := ψ.f n ∘ₗ φ.f n
      face_comp_f i ε := by
        rw [← LinearMap.comp_assoc, ψ.face_comp_f, LinearMap.comp_assoc, φ.face_comp_f,
          LinearMap.comp_assoc]
      degen_comp_f i := by
        rw [← LinearMap.comp_assoc, ψ.degen_comp_f, LinearMap.comp_assoc, φ.degen_comp_f,
          LinearMap.comp_assoc] }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {A} {B C : CubicalModule.{v} R}

@[ext]
theorem hom_ext {φ ψ : A ⟶ B} (h : ∀ n, φ.f n = ψ.f n) : φ = ψ :=
  Hom.ext (funext h)

@[simp]
theorem id_f (n : ℕ) : Hom.f (𝟙 A) n = .id :=
  (rfl)

@[simp]
theorem comp_f (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) : (φ ≫ ψ).f n = ψ.f n ∘ₗ φ.f n :=
  (rfl)

@[simp]
theorem Hom.face_f (φ : A ⟶ B) {n : ℕ} (i : Fin (n + 1)) (ε : Bool) (x : A.X (n + 1)) :
    B.face i ε (φ.f (n + 1) x) = φ.f n (A.face i ε x) :=
  congr($(φ.face_comp_f i ε) x)

@[simp]
theorem Hom.degen_f (φ : A ⟶ B) {n : ℕ} (i : Fin (n + 1)) (x : A.X n) :
    B.degen i (φ.f n x) = φ.f (n + 1) (A.degen i x) :=
  congr($(φ.degen_comp_f i) x)

/-- A morphism of cubical modules commutes with the cubical boundary. -/
@[simp]
theorem Hom.boundary_f (φ : A ⟶ B) {n : ℕ} (x : A.X (n + 1)) :
    B.boundary n (φ.f (n + 1) x) = φ.f n (A.boundary n x) := by
  simp [boundary_apply, faceDiff_apply]

theorem Hom.boundary_comp_f (φ : A ⟶ B) (n : ℕ) :
    B.boundary n ∘ₗ φ.f (n + 1) = φ.f n ∘ₗ A.boundary n :=
  LinearMap.ext φ.boundary_f

/-- The **cubical boundary complex functor**, sending a cubical module to its cubical boundary
complex. -/
@[expose] def complexFunctor : CubicalModule.{v} R ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj A := A.complex
  map φ := ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (φ.f n)) fun n ↦ by
    rw [complex_d, complex_d]
    exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq (φ.boundary_comp_f n)

@[simp]
theorem complexFunctor_obj : complexFunctor.obj A = A.complex :=
  (rfl)

@[simp]
theorem complexFunctor_map_f_apply (φ : A ⟶ B) (n : ℕ) (x : A.X n) :
    (complexFunctor.map φ).f n x = φ.f n x :=
  (rfl)


section const

variable (M : ModuleCat.{v} R)

/-- The **constant cubical module** on `M`: every module of cubes is `M`, and every face and
degeneracy is the identity. -/
@[expose] def const : CubicalModule.{v} R where
  X _ := M
  face _ _ := .id
  degen _ := .id
  face_comp_face _ _ _ _ := rfl
  face_comp_degen_self _ _ := rfl
  face_comp_degen _ _ _ := rfl
  degen_comp_degen _ _ := rfl

@[simp]
theorem const_X (n : ℕ) : (const M).X n = M :=
  (rfl)

@[simp]
theorem const_face {n : ℕ} (i : Fin (n + 1)) (ε : Bool) : (const M).face i ε = .id :=
  (rfl)

@[simp]
theorem const_degen {n : ℕ} (i : Fin (n + 1)) : (const M).degen i = .id :=
  (rfl)

/-- The cubical boundary of a constant cubical module vanishes: its two faces in each coordinate
agree. -/
@[simp]
theorem const_boundary (n : ℕ) : (const M).boundary n = 0 := by
  ext x
  simp [boundary_apply, faceDiff_apply]

end const

end CubicalModule

end TauCeti
