/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import TauCeti.Algebra.RingQuot
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Basic
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# Word length in the signed symmetric algebra

The Koszul relations preserve word length, independently of the input degrees. Consequently
`TauCeti.SignedSym.lengthPiece G n`, the span of products of exactly `n` generators, gives an
internal natural-number grading. Mathlib's `GradedAlgebra.proj` supplies its linear projections.
The length-zero projection is the canonical augmentation followed by the coefficient inclusion;
the length-one projection retains generators. These distinguish constant and linear terms in
an orbit-algebra differential, which need not preserve word length.

This is the word decomposition of the free supercommutative algebra in J. Pardon,
*Contact homology and virtual fundamental cycles*, equation (1.1). We use Mathlib's tensor
word-length grading and the homogeneous-ideal quotient construction to descend it. No basis or
assumption on the characteristic is needed.
-/

public section

namespace TauCeti.SignedSym

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V)

/-- The length-`n` piece is the `n`-th submodule power of the generating module's image. -/
def lengthPiece (n : ℕ) : Submodule R (SignedSym G) :=
  (generator G).range ^ n

/-- Word-length pieces are the images of the native tensor word-length pieces. -/
theorem lengthPiece_eq_map (n : ℕ) :
    lengthPiece G n = ((TensorAlgebra.ι R (M := V)).range ^ n).map
      (quotient G).toLinearMap := by
  rw [Submodule.map_pow, ← LinearMap.range_comp, lengthPiece]
  congr 2
  ext x
  simp

/-- A class of length `n` has a tensor representative of length `n`. -/
theorem mem_lengthPiece_iff {n : ℕ} {a : SignedSym G} :
    a ∈ lengthPiece G n ↔ ∃ x ∈ (TensorAlgebra.ι R (M := V)).range ^ n,
      quotient G x = a := by
  simp only [lengthPiece_eq_map, Submodule.mem_map, AlgHom.toLinearMap_apply]

/-- The defining Koszul ideal is homogeneous for word length. -/
theorem isHomogeneous_ker_quotient_length :
    (RingHom.ker (quotient G)).IsHomogeneous
      (fun n : ℕ => (TensorAlgebra.ι R (M := V)).range ^ n) := by
  rw [quotient, AlgHom.ker_coe, RingQuot.mkAlgHom_coe, RingQuot.ker_mkRingHom_eq_span]
  refine TwoSidedIdeal.homogeneous_span _ ?_
  rintro _ ⟨a, b, hab, rfl⟩
  cases hab with
  | swap p q x y hx hy =>
    have h (x y : V) : TensorAlgebra.ι R x * TensorAlgebra.ι R y ∈
        (TensorAlgebra.ι R (M := V)).range ^ (2 : ℕ) := by
      simpa only [pow_two] using Submodule.mul_mem_mul
        (LinearMap.mem_range_self (TensorAlgebra.ι R) x)
        (LinearMap.mem_range_self (TensorAlgebra.ι R) y)
    exact ⟨2, Submodule.sub_mem _ (h x y) (zsmul_mem (h y x) _)⟩

/-- Word-length pieces form an internal direct sum. -/
theorem isInternal_lengthPiece : DirectSum.IsInternal (lengthPiece G) := by
  let I := RingHom.ker (quotient G)
  let e := Ideal.quotientKerAlgEquivOfSurjective (quotient_surjective G)
  let H : InternalGrading R (TensorAlgebra R V ⧸ I) ℕ :=
    ⟨TauCeti.GradedAlgebra.quotientPiece (fun n : ℕ => (TensorAlgebra.ι R).range ^ n) I,
      TauCeti.GradedAlgebra.isInternal_quotientPiece _ _
        (isHomogeneous_ker_quotient_length G)⟩
  have hp : (H.map e.toLinearEquiv).piece = lengthPiece G := by
    funext n
    rw [InternalGrading.map_piece]
    dsimp only [H]
    rw [TauCeti.GradedAlgebra.quotientPiece_def, ← Submodule.map_comp, lengthPiece_eq_map]
    apply congrArg (((TensorAlgebra.ι R).range ^ n).map)
    exact LinearMap.ext fun x =>
      Ideal.quotientKerAlgEquivOfSurjective_mk (quotient_surjective G) x
  rw [← hp]
  exact (H.map e.toLinearEquiv).isInternal

/-- Multiplication adds word lengths. -/
instance : SetLike.GradedMonoid (lengthPiece G) :=
  inferInstanceAs (SetLike.GradedMonoid (fun n : ℕ => (generator G).range ^ n))

/-- The signed symmetric algebra is internally graded by word length. -/
noncomputable instance : GradedAlgebra (lengthPiece G) :=
  (isInternal_lengthPiece G).gradedAlgebra

@[simp]
theorem lengthPiece_zero : lengthPiece G 0 = 1 := pow_zero _

@[simp]
theorem lengthPiece_one : lengthPiece G 1 = (generator G).range := pow_one _

/-- A generator has word length one, whatever its input degree. -/
theorem generator_mem_lengthPiece (x : V) : generator G x ∈ lengthPiece G 1 := by
  rw [lengthPiece_one]
  exact LinearMap.mem_range_self _ x

/-- The coefficient inclusion identifies the length-zero piece. -/
theorem mem_lengthPiece_zero_iff {a : SignedSym G} :
    a ∈ lengthPiece G 0 ↔ ∃ r : R, algebraMap R (SignedSym G) r = a := by
  rw [lengthPiece_zero, Submodule.mem_one]

/-- Induction in a fixed word length, starting from scalars and prepending generators. -/
@[elab_as_elim]
theorem length_induction {P : ℕ → SignedSym G → Prop}
    (scalar : ∀ r, P 0 (algebraMap R (SignedSym G) r))
    (add : ∀ n a b, P n a → P n b → P n (a + b))
    (cons : ∀ n x a, P n a → P (n + 1) (generator G x * a))
    {n : ℕ} {a : SignedSym G} (ha : a ∈ lengthPiece G n) : P n a := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => exact scalar r
  | add a b n _ _ ha hb => exact add n a b ha hb
  | mem_mul a ha n b _ hb =>
    obtain ⟨x, rfl⟩ := ha
    exact cons n x b hb

/-- The augmentation vanishes on every positive word length. -/
theorem augmentation_eq_zero_of_mem_lengthPiece {n : ℕ} {a : SignedSym G}
    (hn : n ≠ 0) (ha : a ∈ lengthPiece G n) : augmentation G a = 0 := by
  refine length_induction G (P := fun n a => n ≠ 0 → augmentation G a = 0)
    (fun r hn => (hn rfl).elim) (fun n a b ha hb hn => ?_)
    (fun n x a _ _ => ?_) ha hn
  · simp [ha hn, hb hn]
  · simp

/-- On the length-zero piece, augmentation is inverse to the coefficient inclusion. -/
theorem algebraMap_augmentation_of_mem_lengthPiece_zero {a : SignedSym G}
    (ha : a ∈ lengthPiece G 0) :
    algebraMap R (SignedSym G) (augmentation G a) = a := by
  obtain ⟨r, rfl⟩ := (mem_lengthPiece_zero_iff G).mp ha
  simp

/-- Projection of a homogeneous word selects precisely its word length. -/
theorem decompose_lengthPiece_of_mem {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) (m : ℕ) :
    (DirectSum.decompose (lengthPiece G) a m : SignedSym G) = if m = n then a else 0 := by
  classical
  rw [DirectSum.decompose_of_mem _ ha]
  split_ifs with h
  · subst m
    simp
  · simp [DirectSum.of_eq_of_ne _ _ _ h]

/-- The length-one projection fixes generators; every other length projection kills them. -/
@[simp]
theorem decompose_lengthPiece_generator (n : ℕ) (x : V) :
    (DirectSum.decompose (lengthPiece G) (generator G x) n : SignedSym G) =
      if n = 1 then generator G x else 0 :=
  decompose_lengthPiece_of_mem G (generator_mem_lengthPiece G x) n

/-- The constant projection is augmentation followed by the coefficient inclusion. -/
@[simp]
theorem decompose_lengthPiece_zero (a : SignedSym G) :
    (DirectSum.decompose (lengthPiece G) a 0 : SignedSym G) =
      algebraMap R (SignedSym G) (augmentation G a) := by
  induction a using DirectSum.Decomposition.inductionOn (lengthPiece G) with
  | zero => simp
  | @homogeneous n a =>
    by_cases hn : n = 0
    · subst n
      rw [decompose_lengthPiece_of_mem G a.2, ite_eq_left rfl,
        algebraMap_augmentation_of_mem_lengthPiece_zero G a.2]
    · rw [decompose_lengthPiece_of_mem G a.2, ite_eq_right (Ne.symm hn),
        augmentation_eq_zero_of_mem_lengthPiece G hn a.2, map_zero]
  | add a b ha hb =>
    simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, map_add, ha, hb]

section Map

variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W)

/-- A map induced from the generators preserves word length. -/
theorem isHomogeneous_map_length (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    LinearMap.IsHomogeneous (map G H f hf).toLinearMap (lengthPiece G) (lengthPiece H) 0 := by
  refine LinearMap.isHomogeneous_def.2 fun n a ha => ?_
  simp only [add_zero, AlgHom.toLinearMap_apply]
  refine length_induction G
    (P := fun n a => map G H f hf a ∈ lengthPiece H n) ?_ ?_ ?_ ha
  · intro r
    rw [AlgHom.commutes, lengthPiece_zero]
    exact Submodule.algebraMap_mem r
  · intro n a b ha hb
    simpa only [map_add] using add_mem ha hb
  · intro n x a ha
    rw [map_mul, map_generator]
    simpa only [add_comm] using
      SetLike.mul_mem_graded (generator_mem_lengthPiece H (f x)) ha

/-- Word-length projections commute with maps induced by graded linear maps. -/
@[simp]
theorem decompose_lengthPiece_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) (n : ℕ) (a : SignedSym G) :
    (DirectSum.decompose (lengthPiece H) (map G H f hf a) n : SignedSym H) =
      map G H f hf (DirectSum.decompose (lengthPiece G) a n : SignedSym G) := by
  have h := (isHomogeneous_map_length G H f hf).map_decompose n a
  rw [add_zero] at h
  simpa only [AlgHom.toLinearMap_apply] using h.symm

end Map

end TauCeti.SignedSym
