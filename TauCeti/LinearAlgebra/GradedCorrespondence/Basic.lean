/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Prod

/-!
# Homogeneous lifts and graph correspondences

A graded correspondence is a span of linear maps to two decomposed modules, with chosen
sections on admissible homogeneous pieces. Projecting a lifted input to the opposite
module gives its homogeneous transfers. The lifts are indexed only by admissible degrees;
joint injectivity of the span is an additional property, not part of the data.

Every linear equivalence gives such a correspondence with all degrees admissible. Its
transfers are exactly the homogeneous components of the equivalence and its inverse.
This models propagation of homogeneous coefficients across an invertible identification,
without requiring that identification to preserve degrees.

The constructions use Mathlib's `DirectSum.decomposeLinearEquiv` and `DirectSum.component`.

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
-/

public section

namespace TauCeti

variable {R B U V ι κ : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]

/-- A linear span with chosen lifts of the admissible homogeneous pieces on both sides.
The admissible sets `I` and `J` determine the domains of the lifts. Decompositions of
`𝒰` and `𝒱` are supplied when forming homogeneous transfers. -/
@[ext]
structure GradedCorrespondence (𝒰 : ι → Submodule R U) (𝒱 : κ → Submodule R V)
    (I : Set ι) (J : Set κ) where
  /-- The map to the left module. -/
  left : B →ₗ[R] U
  /-- The map to the right module. -/
  right : B →ₗ[R] V
  /-- The chosen lift on each admissible left piece. -/
  liftLeft : (i : I) → 𝒰 i →ₗ[R] B
  /-- The chosen lift on each admissible right piece. -/
  liftRight : (j : J) → 𝒱 j →ₗ[R] B
  /-- A left lift is a section of the left map on its homogeneous piece. -/
  left_liftLeft : ∀ i, left.comp (liftLeft i) = (𝒰 i).subtype
  /-- A right lift is a section of the right map on its homogeneous piece. -/
  right_liftRight : ∀ j, right.comp (liftRight j) = (𝒱 j).subtype

namespace GradedCorrespondence

variable {𝒰 : ι → Submodule R U} {𝒱 : κ → Submodule R V} {I : Set ι} {J : Set κ}

/-- Reverse the two legs, including their admissible degrees and lifts. -/
def symm (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    GradedCorrespondence (B := B) 𝒱 𝒰 J I where
  left := C.right
  right := C.left
  liftLeft := C.liftRight
  liftRight := C.liftLeft
  left_liftLeft := C.right_liftRight
  right_liftRight := C.left_liftLeft

@[simp] theorem symm_left (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    C.symm.left = C.right := (rfl)

@[simp] theorem symm_right (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    C.symm.right = C.left := (rfl)

@[simp] theorem symm_liftLeft (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (j : J) : C.symm.liftLeft j = C.liftRight j := (rfl)

@[simp] theorem symm_liftRight (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) : C.symm.liftRight i = C.liftLeft i := (rfl)

@[simp] theorem symm_symm (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    C.symm.symm = C := (rfl)

@[simp] theorem left_liftLeft_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (a : 𝒰 i) : C.left (C.liftLeft i a) = a :=
  DFunLike.congr_fun (C.left_liftLeft i) a

@[simp] theorem right_liftRight_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (j : J) (a : 𝒱 j) : C.right (C.liftRight j a) = a :=
  DFunLike.congr_fun (C.right_liftRight j) a

section Transfer

variable [DecidableEq κ] [DirectSum.Decomposition 𝒱]

/-- Transfer from an admissible left piece to a right homogeneous piece.
The target degree need not be admissible. Right-to-left transfer is `C.symm.transfer`. -/
noncomputable def transfer (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (j : κ) : 𝒰 i →ₗ[R] 𝒱 j :=
  (DirectSum.component R κ (fun j => 𝒱 j) j).comp
    ((DirectSum.decomposeLinearEquiv 𝒱).toLinearMap.comp (C.right.comp (C.liftLeft i)))

/-- Evaluate a transfer by lifting, crossing the span and taking a component. -/
@[simp] theorem transfer_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (j : κ) (a : 𝒰 i) :
    C.transfer i j a = DirectSum.decompose 𝒱 (C.right (C.liftLeft i a)) j := (rfl)

/-- Only finitely many homogeneous outputs of one input are nonzero. -/
theorem finite_transfer_support (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (a : 𝒰 i) :
    {j | C.transfer i j a ≠ 0}.Finite := by
  simpa only [transfer_apply] using
    (DirectSum.decompose 𝒱 (C.right (C.liftLeft i a))).finite_support

/-- Summing all homogeneous outputs recovers the opposite image of the chosen lift. -/
theorem sum_transfer [∀ j (a : 𝒱 j), Decidable (a ≠ 0)] (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (a : 𝒰 i) :
    ∑ j ∈ (DirectSum.decompose 𝒱 (C.right (C.liftLeft i a))).support,
      (C.transfer i j a : V) = C.right (C.liftLeft i a) := by
  classical
  simp only [transfer_apply, DirectSum.sum_support_decompose]

end Transfer

/-- The graph of a linear equivalence, with all degrees admissible on both sides.
The middle module is `U`; the right lift uses the inverse equivalence. -/
def graph (𝒰 : ι → Submodule R U) (𝒱 : κ → Submodule R V) (e : U ≃ₗ[R] V) :
    GradedCorrespondence (B := U) 𝒰 𝒱 Set.univ Set.univ where
  left := LinearMap.id
  right := e.toLinearMap
  liftLeft i := (𝒰 i).subtype
  liftRight j := e.symm.toLinearMap.comp (𝒱 j).subtype
  left_liftLeft _ := LinearMap.id_comp _
  right_liftRight _ := by ext; simp

@[simp] theorem graph_left (e : U ≃ₗ[R] V) :
    (graph 𝒰 𝒱 e).left = LinearMap.id := (rfl)

@[simp] theorem graph_right (e : U ≃ₗ[R] V) :
    (graph 𝒰 𝒱 e).right = e.toLinearMap := (rfl)

@[simp] theorem graph_liftLeft (e : U ≃ₗ[R] V) (i : (Set.univ : Set ι)) :
    (graph 𝒰 𝒱 e).liftLeft i = (𝒰 i).subtype := (rfl)

@[simp] theorem graph_liftRight (e : U ≃ₗ[R] V) (j : (Set.univ : Set κ)) :
    (graph 𝒰 𝒱 e).liftRight j = e.symm.toLinearMap.comp (𝒱 j).subtype := (rfl)

/-- The two maps of a graph correspondence are jointly injective. -/
theorem graph_injective (e : U ≃ₗ[R] V) :
    Function.Injective ((graph 𝒰 𝒱 e).left.prod (graph 𝒰 𝒱 e).right) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Forward graph transfer is the indicated component of the equivalence. -/
theorem graph_transfer_apply [DecidableEq κ] [DirectSum.Decomposition 𝒱]
    (e : U ≃ₗ[R] V) (i : (Set.univ : Set ι)) (j : κ) (a : 𝒰 i) :
    (graph 𝒰 𝒱 e).transfer i j a = DirectSum.decompose 𝒱 (e a) j := (rfl)

/-- Backward graph transfer is the indicated component of the inverse equivalence. -/
theorem graph_symm_transfer_apply [DecidableEq ι] [DirectSum.Decomposition 𝒰]
    (e : U ≃ₗ[R] V) (j : (Set.univ : Set κ)) (i : ι) (a : 𝒱 j) :
    (graph 𝒰 𝒱 e).symm.transfer j i a = DirectSum.decompose 𝒰 (e.symm a) i := (rfl)

end GradedCorrespondence
end TauCeti
