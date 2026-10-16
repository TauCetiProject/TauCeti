/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Graded base change of symmetric algebras

The canonical equivalence `S ⊗[R] Sym(M) ≃ Sym(S ⊗[R] M)` identifies the scalar extension
of every homogeneous piece with the corresponding homogeneous piece over `S`. Both directions
are bundled as graded algebra maps, so the equivalence can be used on projective spectra.
This supplies the homogeneous-coordinate comparison needed to construct families of projective
linear transformations. No freeness, flatness, or finite generation of the module is required.

The underlying equivalence is `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`; the grading
on its source is Mathlib's `GradedAlgebra.baseChange`.

The image computation follows the image-of-powers argument in
`TauCeti.exteriorAlgebraEquivBaseChange_map_exteriorPower`, and the tensor-product comparison
follows `TauCeti.exteriorPower.equivBaseChange`, using
`Submodule.baseChange_map` and `Submodule.baseChange_pow` over commutative semirings.

## Main declarations

* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivBaseChange`: symmetric powers commute
  with scalar extension, in tensor-product form.
* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleBaseChangeEquiv`: the equivalence between
  homogeneous submodules of the ambient algebras.
* `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHom` and
  `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHomSymm`: the mutually inverse graded maps.
* `TensorProduct.scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff` and
  `SymmetricAlgebra.scalarTensorBialgEquiv_symm_mem_baseChange_iff`: preservation and reflection
  of homogeneous degree in both directions.
* `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap` and
  its inverse counterpart: the degree-zero comparisons preserve scalars.

Naturality is provided by `LinearMap.scalarTensorBialgEquiv_comp_map` in
`TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The image of the scalar-extended degree-`n` piece is exactly the degree-`n` piece of the
symmetric algebra on the scalar-extended module. -/
-- Compare degrees before `Submodule.baseChange_pow` expands the source piece.
@[simp↓]
theorem map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule (n : ℕ) :
    ((homogeneousSubmodule R M n).baseChange S).map
        (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearMap =
      homogeneousSubmodule S (S ⊗[R] M) n := by
  simp only [homogeneousSubmodule, Submodule.baseChange_pow]
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow]
  congr 1
  rw [LinearMap.baseChange_range, ← LinearMap.range_comp]
  congr 1
  ext m
  simp

/-- The base-change equivalence preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule {n : ℕ}
    {x : S ⊗[R] SymmetricAlgebra R M}
    (hx : x ∈ (homogeneousSubmodule R M n).baseChange S) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  rw [← map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n]
  exact Submodule.mem_map_of_mem hx

/-- The inverse base-change equivalence also preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_symm_mem_baseChange {n : ℕ}
    {x : SymmetricAlgebra S (S ⊗[R] M)}
    (hx : x ∈ homogeneousSubmodule S (S ⊗[R] M) n) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
      (homogeneousSubmodule R M n).baseChange S := by
  rw [← map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [AlgEquiv.toLinearMap_apply, BialgEquiv.coe_toAlgEquiv,
    BialgEquiv.symm_apply_apply, SetLike.mem_coe] using hy

end TauCeti.SymmetricAlgebra

namespace TensorProduct

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Membership in a homogeneous piece is preserved and reflected by scalar extension. -/
@[simp]
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff {n : ℕ}
    (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n ↔
      x ∈ (homogeneousSubmodule R M n).baseChange S := by
  constructor
  · intro hx
    simpa only [BialgEquiv.symm_apply_apply] using
      scalarTensorBialgEquiv_symm_mem_baseChange hx
  · exact scalarTensorBialgEquiv_mem_homogeneousSubmodule

end TensorProduct

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Scalar extension identifies the degree-`n` homogeneous pieces as `S`-modules. -/
noncomputable def homogeneousSubmoduleBaseChangeEquiv (n : ℕ) :
    (homogeneousSubmodule R M n).baseChange S ≃ₗ[S]
      homogeneousSubmodule S (S ⊗[R] M) n :=
  (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearEquiv.ofSubmodules _ _
    (map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n)

/-- The degreewise equivalence is the restriction of the scalar-extension equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_apply (n : ℕ)
    (x : (homogeneousSubmodule R M n).baseChange S) :
    (homogeneousSubmoduleBaseChangeEquiv n x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S) x := by
  exact LinearEquiv.ofSubmodules_apply _ _ x

/-- The inverse degreewise equivalence is the restriction of the inverse scalar-extension
equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_symm_apply (n : ℕ)
    (x : homogeneousSubmodule S (S ⊗[R] M) n) :
    ((homogeneousSubmoduleBaseChangeEquiv n).symm x : S ⊗[R] SymmetricAlgebra R M) =
      (scalarTensorBialgEquiv (k := R) (K := S)).symm x := by
  exact LinearEquiv.ofSubmodules_symm_apply _ _ x

/-- Scalar extension of the inclusion of a homogeneous piece remains injective. -/
theorem homogeneousSubmodule_baseChange_subtype_injective (n : ℕ) :
    Function.Injective ((homogeneousSubmodule R M n).subtype.baseChange S) := by
  intro x y h
  exact DirectSum.toBaseChange_injective (S := S) (homogeneousSubmodule R M) n
    (Subtype.ext h)

/-- Symmetric powers commute with scalar extension, without a flatness assumption. -/
noncomputable def homogeneousSubmoduleEquivBaseChange (n : ℕ) :
    homogeneousSubmodule S (S ⊗[R] M) n ≃ₗ[S] S ⊗[R] homogeneousSubmodule R M n :=
  (homogeneousSubmoduleBaseChangeEquiv n).symm.trans
    (LinearEquiv.ofInjective ((homogeneousSubmodule R M n).subtype.baseChange S)
      (homogeneousSubmodule_baseChange_subtype_injective n)).symm

/-- The tensor-product comparison agrees with the inverse ambient comparison after inclusion. -/
@[simp]
theorem subtype_baseChange_homogeneousSubmoduleEquivBaseChange (n : ℕ)
    (x : homogeneousSubmodule S (S ⊗[R] M) n) :
    (homogeneousSubmodule R M n).subtype.baseChange S
        (homogeneousSubmoduleEquivBaseChange n x) =
      (scalarTensorBialgEquiv (k := R) (K := S)).symm (x : SymmetricAlgebra S (S ⊗[R] M)) := by
  exact (LinearEquiv.ofInjective_symm_apply _
    (h := homogeneousSubmodule_baseChange_subtype_injective n) _).trans
      (coe_homogeneousSubmoduleBaseChangeEquiv_symm_apply n x)

/-- The inverse tensor-product comparison agrees with the forward ambient comparison. -/
@[simp]
theorem coe_homogeneousSubmoduleEquivBaseChange_symm_apply (n : ℕ)
    (x : S ⊗[R] homogeneousSubmodule R M n) :
    ((homogeneousSubmoduleEquivBaseChange n).symm x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        ((homogeneousSubmodule R M n).subtype.baseChange S x) := by
  exact coe_homogeneousSubmoduleBaseChangeEquiv_apply n _

/-- The canonical scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHom :
    (fun n ↦ (homogeneousSubmodule R M n).baseChange S) →ₐᵍ[S]
      homogeneousSubmodule S (S ⊗[R] M) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_mem_homogeneousSubmodule

/-- The inverse scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHomSymm :
    homogeneousSubmodule S (S ⊗[R] M) →ₐᵍ[S]
      (fun n ↦ (homogeneousSubmodule R M n).baseChange S) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm.toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_symm_mem_baseChange

end TauCeti.SymmetricAlgebra

namespace TensorProduct

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The forward graded map is the existing scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHom_apply (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorGradedAlgHom x = scalarTensorBialgEquiv (k := R) (K := S) x := (rfl)

end TensorProduct

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The inverse graded map is the inverse scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHomSymm_apply (x : SymmetricAlgebra S (S ⊗[R] M)) :
    scalarTensorGradedAlgHomSymm x = (scalarTensorBialgEquiv (k := R) (K := S)).symm x := (rfl)

end SymmetricAlgebra

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The inverse graded map is a right inverse of the forward graded map. -/
theorem scalarTensorGradedAlgHom_rightInverse :
    Function.RightInverse
      (scalarTensorGradedAlgHomSymm (R := R) (S := S) (M := M))
      scalarTensorGradedAlgHom := by
  intro x
  simp only [TensorProduct.scalarTensorGradedAlgHom_apply,
    _root_.SymmetricAlgebra.scalarTensorGradedAlgHomSymm_apply, BialgEquiv.apply_symm_apply]

/-- The inverse graded map is a left inverse of the forward graded map. -/
theorem scalarTensorGradedAlgHom_leftInverse :
    Function.LeftInverse
      (scalarTensorGradedAlgHomSymm (R := R) (S := S) (M := M))
      scalarTensorGradedAlgHom := by
  intro x
  simp only [TensorProduct.scalarTensorGradedAlgHom_apply,
    _root_.SymmetricAlgebra.scalarTensorGradedAlgHomSymm_apply, BialgEquiv.symm_apply_apply]

/-- On degree zero, the forward comparison preserves each scalar from `S`. -/
@[simp]
theorem scalarTensorGradedAlgHom_gradedZeroRingHom_algebraMap (s : S) :
    scalarTensorGradedAlgHom.toGradedRingHom.gradedZeroRingHom
        (algebraMap S ((homogeneousSubmodule R M 0).baseChange S) s) =
      algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0) s := by
  apply Subtype.ext
  simp only [GradedRingHom.gradedZeroRingHom_apply_coe,
    SetLike.GradeZero.coe_algebraMap]
  -- Mathlib has no coercion lemma for `GradedAlgHom.toGradedRingHom`; identify its
  -- underlying function and scalar inclusions before using the computation lemma.
  change scalarTensorGradedAlgHom (algebraMap S _ s) = algebraMap S _ s
  rw [TensorProduct.scalarTensorGradedAlgHom_apply]
  exact (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.commutes s

/-- On degree zero, the inverse comparison preserves each scalar from `S`. -/
@[simp]
theorem scalarTensorGradedAlgHomSymm_gradedZeroRingHom_algebraMap (s : S) :
    scalarTensorGradedAlgHomSymm.toGradedRingHom.gradedZeroRingHom
        (algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0) s) =
      algebraMap S ((homogeneousSubmodule R M 0).baseChange S) s := by
  apply Subtype.ext
  simp only [GradedRingHom.gradedZeroRingHom_apply_coe,
    SetLike.GradeZero.coe_algebraMap]
  -- As above, identify the underlying function of `toGradedRingHom` and scalar inclusions.
  change scalarTensorGradedAlgHomSymm (algebraMap S _ s) = algebraMap S _ s
  rw [_root_.SymmetricAlgebra.scalarTensorGradedAlgHomSymm_apply]
  exact (scalarTensorBialgEquiv (k := R) (K := S)).symm.toAlgEquiv.commutes s

/-- On degree zero, the forward comparison preserves the scalar map from `S`. -/
theorem scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap :
    scalarTensorGradedAlgHom.toGradedRingHom.gradedZeroRingHom.comp
        (algebraMap S ((homogeneousSubmodule R M 0).baseChange S)) =
      algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0) := by
  apply RingHom.ext
  intro s
  exact scalarTensorGradedAlgHom_gradedZeroRingHom_algebraMap (R := R) (M := M) s

/-- On degree zero, the inverse comparison preserves the scalar map from `S`. -/
theorem scalarTensorGradedAlgHomSymm_gradedZeroRingHom_comp_algebraMap :
    scalarTensorGradedAlgHomSymm.toGradedRingHom.gradedZeroRingHom.comp
        (algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0)) =
      algebraMap S ((homogeneousSubmodule R M 0).baseChange S) := by
  apply RingHom.ext
  intro s
  exact scalarTensorGradedAlgHomSymm_gradedZeroRingHom_algebraMap (R := R) (M := M) s

end TauCeti.SymmetricAlgebra

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The inverse comparison preserves and reflects homogeneous degree as well. -/
-- Compare degrees before `Submodule.baseChange_pow` expands the source piece.
@[simp↓]
theorem scalarTensorBialgEquiv_symm_mem_baseChange_iff {n : ℕ}
    (x : SymmetricAlgebra S (S ⊗[R] M)) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
        (homogeneousSubmodule R M n).baseChange S ↔
      x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  rw [← TensorProduct.scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff,
    BialgEquiv.apply_symm_apply]

end SymmetricAlgebra
