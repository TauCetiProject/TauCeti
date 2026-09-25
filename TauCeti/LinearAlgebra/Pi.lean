/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Supports, splittings and determinants of finite dependent products

For `s : Set ι`, the submodule `Submodule.pi sᶜ (fun _ ↦ ⊥)` of `ι → M` consists of the families
vanishing outside `s` — the `Pi` analogue of `Finsupp.supported`. This file records that
complementary supports meet in `⊥`. It also records the linear splitting of a dependent product
along a predicate on the indices, and the determinant of a coordinatewise endomorphism of a finite
dependent product, which is used in finite-product norm calculations.

Mathlib has `Set.disjoint_pi`, but that is about `Set.pi` and characterises disjointness through
the fibres; it says nothing about the submodules cut out by a support condition.

## Main results

* `Submodule.disjoint_pi_compl_bot_of_disjoint`: disjoint index sets give disjoint submodules of
  families vanishing outside them.
* `LinearEquiv.piEquivPiSubtypeProd`: `Equiv.piEquivPiSubtypeProd` as a linear equivalence,
  splitting `∀ i, M i` into the factors indexed by `p` and by `¬p`.
* `LinearMap.det_pi_of_apply_eq_dependent`: the determinant of a coordinatewise endomorphism of a
  finite dependent product is the product of the determinants on its factors.
-/

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]

/-- **Disjoint sets of indices give disjoint submodules of families vanishing outside them.**
A family vanishing outside `s` and outside `t` at once, for `s` and `t` disjoint, vanishes
everywhere. The submodules are `Submodule.pi` at the zero submodule.

Nothing here is topological or about any particular index type; the Huber two-sided series use it
at `ι = ℤ` with `s` and `t` the non-negative and negative degrees. -/
public theorem disjoint_pi_compl_bot_of_disjoint {ι : Type*} {s t : Set ι} (h : Disjoint s t) :
    Disjoint (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (Submodule.pi tᶜ fun _ ↦ (⊥ : Submodule A M)) :=
  Submodule.disjoint_def.mpr fun f hs ht ↦ funext fun i ↦ by
    by_cases hi : i ∈ s
    · exact ht i (Set.disjoint_left.mp h hi)
    · exact hs i hi

end Submodule

namespace LinearEquiv

variable (R : Type*) {ι : Type*} [Semiring R] (p : ι → Prop) [DecidablePred p] (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Splits the indices of the module `∀ i, M i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `LinearEquiv`. -/
public def piEquivPiSubtypeProd :
    ((i : ι) → M i) ≃ₗ[R] ((i : {x : ι // p x}) → M i) × ((i : {x : ι // ¬p x}) → M i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
public theorem piEquivPiSubtypeProd_apply (f : (i : ι) → M i) :
    piEquivPiSubtypeProd R p M f =
      (fun i : {x : ι // p x} ↦ f i, fun i : {x : ι // ¬p x} ↦ f i) := (rfl)

@[simp]
public theorem piEquivPiSubtypeProd_symm_apply
    (f : ((i : {x : ι // p x}) → M i) × ((i : {x : ι // ¬p x}) → M i)) (i : ι) :
    (piEquivPiSubtypeProd R p M).symm f i = if h : p i then f.1 ⟨i, h⟩ else f.2 ⟨i, h⟩ := (rfl)

end LinearEquiv

namespace TauCeti

open scoped BigOperators

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- The determinant of a coordinatewise endomorphism of a finite dependent product. -/
public theorem _root_.LinearMap.det_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)]
    (T : ((i : ι) → M i) →ₗ[R] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[R] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    T.det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex R (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex R (M i)) R ((i : ι) → M i) :=
    Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have hmatrix :
      (LinearMap.toMatrix B B T) =
        Matrix.blockDiagonal' (fun i ↦ LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [LinearMap.toMatrix_apply', B, b, Pi.basis_apply, Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst i₂
      simp [hT]
    · simp [hT, h]
  rw [hmatrix]
  let _ : LinearOrder ι := Equiv.linearOrder (Fintype.equivFin ι)
  rw [(Matrix.blockTriangular_blockDiagonal' _).det_fintype]
  apply Finset.prod_congr rfl
  intro i hi
  let e : Module.Free.ChooseBasisIndex R (M i) ≃
      {a : Σ i, Module.Free.ChooseBasisIndex R (M i) // a.1 = i} :=
    { toFun := fun j ↦ ⟨⟨i, j⟩, rfl⟩
      invFun := fun a ↦ cast (by rw [a.2]) a.1.2
      left_inv := by intro j; rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rcases a with ⟨⟨a, j⟩, ha⟩
        dsimp at ha
        subst a
        rfl }
  rw [← LinearMap.det_toMatrix (b i)]
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j k
  rcases j with ⟨⟨j₁, j₂⟩, hj⟩
  rcases k with ⟨⟨k₁, k₂⟩, hk⟩
  dsimp at hj hk
  subst j₁
  subst k₁
  simp [e, Matrix.toSquareBlock_def, Matrix.reindex]

end TauCeti
